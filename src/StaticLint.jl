module StaticLint
using SymbolServer
using CSTParser
using CSTParser: isidentifier
using CSTParser: Scope, Binding, EXPR, PUNCTUATION, IDENTIFIER, KEYWORD, OPERATOR
using CSTParser: Call, UnaryOpCall, BinaryOpCall, WhereOpCall, Import, Using, Export, TopLevel, ModuleH, BareModule, Quote, Quotenode, MacroName, MacroCall, Macro, x_Str, FileH, Parameters

const NoReference = Binding("0NoReference", nothing, nothing, [], nothing)


mutable struct State
    file
    scope::Scope
    delayed::Union{Nothing,Scope}
    ignorewherescope::Bool
    quoted::Bool
    urefs::Dict{Scope,Vector{EXPR}}
    server
end

function (state::State)(x)
    delayed = state.delayed # store previous delayed eval scope
    isquoted = state.quoted
    if quoted(x)
        state.quoted = true
    end
    if state.quoted && unquoted(x)
        state.quoted = false
    end
    # imports
    if x.typ === Using || x.typ === Import
        resolve_import(x, state)
    end
    if x.typ === Export # Allow delayed resolution
        state.delayed = state.scope
    end
    
    #bindings
    add_binding(x, state)

    #macros
    handle_macro(x, state)
    
    # scope
    clear_scope(x)
    s0 = state.scope
    if x.typ === FileH
        x.scope = state.scope
    elseif x.scope isa Scope
        if CSTParser.defines_function(x)
            state.delayed = state.scope # Allow delayed resolution
        end
        x.scope != s0 && (x.scope.parent = s0)
        state.scope = x.scope
        if x.typ === ModuleH # Add default modules to a new module
            state.scope.modules = Dict{String,Any}()
            state.scope.modules["Base"] = getsymbolserver(state.server)["Base"]
            state.scope.modules["Core"] = getsymbolserver(state.server)["Core"]
        end
        if (x.typ === CSTParser.ModuleH || x.typ === CSTParser.BareModule) && x.binding !== nothing # Add reference to out of scope binding (i.e. itself)
            if x.binding !== nothing
                state.scope.names[x.binding.name] = x.binding
            end
        end
        if x.typ === CSTParser.Flatten && x.args[1].typ === CSTParser.Generator && x.args[1].args isa Vector{EXPR} && length(x.args[1].args) > 0 && x.args[1].args[1].typ === CSTParser.Generator
            x.args[1].args[1].scope = nothing
        end
    end
    followinclude(x, state) # follow include
    if state.quoted
        if isidentifier(x) && !hasref(x)
            x.ref = NoReference
        end
    elseif x.typ === CSTParser.Quotenode && length(x.args) == 2 && x.args[1].kind === CSTParser.Tokens.COLON && x.args[2].typ === CSTParser.IDENTIFIER
        x.args[2].ref = NoReference
    elseif (isidentifier(x) && !hasref(x)) || resolvable_macroname(x) || x.typ === x_Str || (x.typ === BinaryOpCall && x.args[2].kind === CSTParser.Tokens.DOT)
        resolved = resolve_ref(x, state.scope)
        if !resolved && state.delayed !== nothing
            if haskey(state.urefs, state.scope)
                push!(state.urefs[state.scope], x)
            else
                state.urefs[state.scope] = EXPR[x]
            end
        end
    end
    # traverse across children (evaluation order)
    if x.typ === CSTParser.BinaryOpCall && (CSTParser.is_assignment(x) && !CSTParser.is_func_call(x.args[1]) || x.args[2].typ === CSTParser.Tokens.DECLARATION) && !(CSTParser.is_assignment(x) && x.args[1].typ === CSTParser.Curly)
        state(x.args[3])
        state(x.args[2])
        state(x.args[1])
    elseif x.typ === CSTParser.WhereOpCall
        @inbounds for i = 3:length(x.args)
            state(x.args[i])
        end
        state(x.args[1])
        state(x.args[2])
    elseif x.typ === CSTParser.Generator
        @inbounds for i = 2:length(x.args)
            state(x.args[i])
        end
        state(x.args[1])
    elseif x.typ === CSTParser.Flatten && x.args !== nothing && length(x.args) === 1 && x.args[1].args !== nothing && length(x.args[1]) >= 3 && length(x.args[1].args[1]) >= 3
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
    state.delayed != delayed && (state.delayed = delayed)
    state.quoted = isquoted
    return state.scope
end

function add_binding(x, state)
    if x.binding isa Binding
        if x.typ === Macro
            state.scope.names[string("@", x.binding.name)] = x.binding
            mn = CSTParser.get_name(x)
            if mn.typ === IDENTIFIER
                mn.ref = x.binding
            end
        else
            if haskey(state.scope.names, x.binding.name)
                x.binding.overwrites = state.scope.names[x.binding.name]
            end
            state.scope.names[x.binding.name] = x.binding
        end
        infer_type(x.binding, state.scope, state.server)
    elseif x.binding isa SymbolServer.SymStore
        state.scope.names[x.val] = x.binding
    end
end

function followinclude(x, state::State)
    if x.typ === Call && x.args[1].typ === IDENTIFIER && x.args[1].val == "include"
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
            getcst(state.file).scope = nothing
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
