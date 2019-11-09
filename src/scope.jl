mutable struct Scope
    parent::Union{Scope,Nothing}
    expr::EXPR
    names::Dict{String,Binding}
    modules::Union{Nothing,Dict{String,Any}}
    ismodule::Bool
end
Scope(expr) = Scope(nothing, expr, Dict{String,Binding}(), nothing, typof(expr) === CSTParser.ModuleH || typof(expr) === CSTParser.BareModule)

function introduces_scope(x::EXPR, state)
    if typof(x) === CSTParser.BinaryOpCall
        if kindof(x.args[2]) === CSTParser.Tokens.EQ && CSTParser.is_func_call(x.args[1])
            return true
        elseif kindof(x.args[2]) === CSTParser.Tokens.EQ && typof(x.args[1]) === CSTParser.Curly
            return true
        elseif kindof(x.args[2]) === CSTParser.Tokens.ANON_FUNC
            return true
        else
            return false
        end
    elseif typof(x) === CSTParser.WhereOpCall
        #unless in func def signature
        return !_in_func_def(x)
    elseif typof(x) === CSTParser.FunctionDef ||
            typof(x) === CSTParser.Macro ||
            typof(x) === CSTParser.For ||
            typof(x) === CSTParser.While ||
            typof(x) === CSTParser.Let ||
            typof(x) === CSTParser.Generator || # and Flatten? 
            typof(x) === CSTParser.Try ||
            typof(x) === CSTParser.Do ||
            typof(x) === CSTParser.ModuleH ||
            typof(x) === CSTParser.BareModule ||
            typof(x) === CSTParser.Abstract ||
            typof(x) === CSTParser.Primitive ||
            typof(x) === CSTParser.Mutable ||
            typof(x) === CSTParser.Struct
        return true
    end
    return false
end


hasscope(x::EXPR) = hasmeta(x) && hasscope(x.meta)
scopeof(x) = nothing
scopeof(x::EXPR) = scopeof(x.meta)
CSTParser.parentof(s::Scope) = s.parent

function setscope!(x::EXPR, s)
    if !hasmeta(x)
        x.meta = Meta()
    end
    x.meta.scope = s
end

function scopes(x::EXPR, state)
    clear_scope(x)
    if scopeof(x) === nothing && introduces_scope(x, state)
        setscope!(x, Scope(x))
    end
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
            # state.scope.names[bindingof(x).name] = bindingof(x)
            add_binding(x, state)
        elseif typof(x) === CSTParser.Flatten && typof(x.args[1]) === CSTParser.Generator && x.args[1].args isa Vector{EXPR} && length(x.args[1].args) > 0 && typof(x.args[1].args[1]) === CSTParser.Generator
            setscope!(x.args[1].args[1], nothing)
        end
    end
    return s0    
end