module StaticLint
using SymbolServer
using CSTParser
using CSTParser: isidentifier
using CSTParser: Scope, Binding, EXPR, PUNCTUATION, IDENTIFIER, KEYWORD, OPERATOR
using CSTParser: Call, UnaryOpCall, BinaryOpCall, WhereOpCall, Import, Using, Export, TopLevel, ModuleH, BareModule, Quote, Quotenode, MacroName, MacroCall, Macro, x_Str, FileH, Parameters
using CSTParser: setparent!, setscope!
# to be removed after CSTParser change
kindof(x::EXPR) = x.kind
kindof(t::CSTParser.Tokens.AbstractToken) = t.kind
valof(x::EXPR) = x.val
typof(x::EXPR) = x.typ
parentof(x::EXPR) = x.parent
parentof(s::Scope) = s.parent
scopeof(x::EXPR) = x.scope
bindingof(x::EXPR) = x.binding
refof(x::EXPR) = x.ref

function setref!(x::EXPR, r)
    x.ref = r
    return x
end


const NoReference = Binding("0NoReference", nothing, nothing, [], nothing)


mutable struct State
    file
    scope::Scope
    delayed::Bool
    ignorewherescope::Bool
    quoted::Bool
    urefs::Vector{EXPR}
    server
end

function (state::State)(x)
    delayed = state.delayed # store states
    isquoted = state.quoted

    if quoted(x)
        state.quoted = true
    elseif state.quoted && unquoted(x)
        state.quoted = false
    end
    # imports
    if typof(x) === Using || typof(x) === Import
        resolve_import(x, state)
    elseif typof(x) === Export # Allow delayed resolution
        state.delayed = true
    end
    
    #bindings
    add_binding(x, state)
    mark_globals(x, state)

    #macros
    handle_macro(x, state)
    
    # scope
    clear_scope(x)
    s0 = state.scope
    if typof(x) === FileH
        setscope!(x, state.scope)
    elseif scopeof(x) isa Scope
        if CSTParser.defines_function(x) || CSTParser.defines_macro(x)
            state.delayed = true # Allow delayed resolution
        end
        scopeof(x) != s0 && setparent!(scopeof(x), s0)
        state.scope = scopeof(x)
        if typof(x) === ModuleH # Add default modules to a new module
            state.scope.modules = Dict{String,Any}()
            state.scope.modules["Base"] = getsymbolserver(state.server)["Base"]
            state.scope.modules["Core"] = getsymbolserver(state.server)["Core"]
        elseif typof(x) === BareModule
            state.scope.modules = Dict{String,Any}()
            state.scope.modules["Core"] = getsymbolserver(state.server)["Core"]
        end
        if (typof(x) === CSTParser.ModuleH || typof(x) === CSTParser.BareModule) && bindingof(x) !== nothing # Add reference to out of scope binding (i.e. itself)
            state.scope.names[bindingof(x).name] = bindingof(x)
        elseif typof(x) === CSTParser.Flatten && typof(x.args[1]) === CSTParser.Generator && x.args[1].args isa Vector{EXPR} && length(x.args[1].args) > 0 && typof(x.args[1].args[1]) === CSTParser.Generator
            setscope!(x.args[1].args[1], nothing)
        end
    end
    followinclude(x, state) # follow include
    if state.quoted
        if isidentifier(x) && !hasref(x)
            setref!(x, NoReference)
        end
    elseif typof(x) === CSTParser.Quotenode && length(x.args) == 2 && kindof(x.args[1]) === CSTParser.Tokens.COLON && typof(x.args[2]) === CSTParser.IDENTIFIER
        setref!(x.args[2], NoReference)
    elseif (isidentifier(x) && !hasref(x)) || resolvable_macroname(x) || typof(x) === x_Str || (typof(x) === BinaryOpCall && kindof(x.args[2]) === CSTParser.Tokens.DOT)
        resolved = resolve_ref(x, state.scope, state)
        if !resolved && (state.delayed || isglobal(valof(x), state.scope))
            push!(state.urefs, x)
        end
    end
    # traverse across children (evaluation order)
    if typof(x) === CSTParser.BinaryOpCall && (CSTParser.is_assignment(x) && !CSTParser.is_func_call(x.args[1]) || typof(x.args[2]) === CSTParser.Tokens.DECLARATION) && !(CSTParser.is_assignment(x) && typof(x.args[1]) === CSTParser.Curly)
        state(x.args[3])
        state(x.args[2])
        state(x.args[1])
    elseif typof(x) === CSTParser.WhereOpCall
        @inbounds for i = 3:length(x.args)
            state(x.args[i])
        end
        state(x.args[1])
        state(x.args[2])
    elseif typof(x) === CSTParser.Generator
        @inbounds for i = 2:length(x.args)
            state(x.args[i])
        end
        state(x.args[1])
    elseif typof(x) === CSTParser.Flatten && x.args !== nothing && length(x.args) === 1 && x.args[1].args !== nothing && length(x.args[1]) >= 3 && length(x.args[1].args[1]) >= 3
        for i = 3:length(x.args[1].args[1].args)
            state(x.args[1].args[1].args[i])
        end
        for i = 3:length(x.args[1].args)
            state(x.args[1].args[i])
        end
        state(x.args[1].args[1].args[1])
    elseif x.args !== nothing
        @inbounds for i in 1:length(x.args)
            state(x.args[i])
        end
    end
    checks(x, state.server)

    # return to previous states
    state.scope != s0 && (state.scope = s0)
    state.delayed = delayed
    state.quoted = isquoted
    return state.scope
end

function add_binding(x, state)
    scope = state.scope
    if bindingof(x) isa Binding
        # check for global marker
        if isglobal(bindingof(x).name, scope)
            scope = _get_global_scope(state.scope)
        end

        if typof(x) === Macro
            scope.names[string("@", bindingof(x).name)] = bindingof(x)
            mn = CSTParser.get_name(x)
            if typof(mn) === IDENTIFIER
                setref!(mn, bindingof(x))
            end
        else
            if haskey(scope.names, bindingof(x).name)
                bindingof(x).overwrites = scope.names[bindingof(x).name]
            end
            scope.names[bindingof(x).name] = bindingof(x)
        end
        infer_type(bindingof(x), scope, state)
    elseif bindingof(x) isa SymbolServer.SymStore
        scope.names[valof(x)] = bindingof(x)
    end
end

isglobal(name, scope) = haskey(scope.names, "#globals") && name in scope.names["#globals"].refs

function mark_globals(x, state)
    if typof(x) === CSTParser.Global
        if !haskey(state.scope.names, "#globals")
            state.scope.names["#globals"] = CSTParser.Binding("#globals", nothing, nothing, String[], nothing)
        end
        if x.args isa Vector{EXPR}
            for i = 2:length(x.args)
                if typof(x.args[i]) === CSTParser.IDENTIFIER && !haskey(state.scope.names, valof(x.args[i]))
                    push!(state.scope.names["#globals"].refs, valof(x.args[i]))
                end
            end
        end
    end
end

function followinclude(x, state::State)
    if typof(x) === Call && typof(x.args[1]) === IDENTIFIER && valof(x.args[1]) == "include"
        path = get_path(x)
        if isempty(path)
        elseif hasfile(state.server, path)
        elseif canloadfile(state.server, path)
            loadfile(state.server, path)
        elseif hasfile(state.server, joinpath(dirname(getpath(state.file)), path))
            path = joinpath(dirname(getpath(state.file)), path)
        elseif canloadfile(state.server, joinpath(dirname(getpath(state.file)), path))
            path = joinpath(dirname(getpath(state.file)), path)
            loadfile(state.server, path,)
        else
            path = ""
        end
        if !isempty(path)
            oldfile = state.file
            state.file = getfile(state.server, path)
            setroot(state.file, getroot(oldfile))
            setscope!(getcst(state.file), nothing)
            state(getcst(state.file))
            state.file = oldfile
        else
            # (printstyled(">>>>Can't follow include", color = :red);printstyled(" $(Expr(x)) from $(dirname(state.path))\n"))
            # error handling for broken `include` here
        end
    end
end

include("server.jl")
include("imports.jl")
include("references.jl")
include("macros.jl")
include("checks.jl")
include("type_inf.jl")
include("utils.jl")
end
