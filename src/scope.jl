mutable struct Scope
    parent::Union{Scope,Nothing}
    expr::EXPR
    names::Dict{String,Binding}
    modules::Union{Nothing,Dict{Symbol,Any}}
    overloaded::Union{Dict,Nothing}
end
Scope(expr) = Scope(nothing, expr, Dict{Symbol,Binding}(), nothing, nothing)
function Base.show(io::IO, s::Scope)
    printstyled(io, typof(s.expr))
    printstyled(io, " ", join(keys(s.names), ","), color=:yellow)
    s.modules isa Dict && printstyled(io, " ", join(keys(s.modules), ","), color=:blue)
    # println(io)
end

function overload_method(scope::Scope, b::Binding, vr::SymbolServer.VarRef)
    if scope.overloaded === nothing
        scope.overloaded = Dict()
    end
    if haskey(scope.overloaded, vr)
        b.prev = scope.overloaded[vr]
        b.prev.next = b
    end
    scope.overloaded[vr] = b
end

"""
scopehasmodule(s::Scope, mname::Symbol)::Bool

Checks whether the module `mname` has been `using`ed in `s`.
"""
scopehasmodule(s::Scope, mname::Symbol) = s.modules !== nothing && haskey(s.modules, mname)

"""
    addmoduletoscope!(s, m, [mname::Symbol])

Adds module `m` to the list of used modules in scope `s`.
"""
function addmoduletoscope!(s::Scope, m, mname::Symbol)
    if s.modules === nothing
        s.modules = Dict{Symbol,Any}()
    end
    s.modules[mname] = m
end
addmoduletoscope!(s::Scope, m::SymbolServer.ModuleStore) = addmoduletoscope!(s, m, m.name.name)
addmoduletoscope!(s::Scope, m::EXPR) =  CSTParser.defines_module(m) && addmoduletoscope!(s, scopeof(m), Symbol(valof(CSTParser.get_name(m))))
addmoduletoscope!(s::Scope, s1::Scope) = CSTParser.defines_module(s1.expr) && addmoduletoscope!(s, s1, Symbol(valof(CSTParser.get_name(s1.expr))))


getscopemodule(s::Scope, m::Symbol) = s.modules[m]

"""
    scopehasbinding(s::Scope, n::String)

Checks whether s has a binding for variable named `n`.
"""
scopehasbinding(s::Scope, n::String) = haskey(s.names, n)

"""
    introduces_scope(x::EXPR, state)

Does this expression introduce a new scope?
"""
function introduces_scope(x::EXPR, state)
    # TODO: remove unused 2nd argument.
    if is_binary_call(x)
        if kindof(x[2]) === CSTParser.Tokens.EQ && CSTParser.is_func_call(x[1])
            return true
        elseif kindof(x[2]) === CSTParser.Tokens.EQ && is_curly(x[1])
            return true
        elseif kindof(x[2]) === CSTParser.Tokens.ANON_FUNC
            return true
        else
            return false
        end
    elseif is_where(x)
        # unless in func def signature
        return !_in_func_def(x)
    elseif is_tuple(x) && length(x) > 2 && ispunctuation(x[1]) && is_assignment(x[2])
        return true
    elseif typof(x) === CSTParser.FunctionDef ||
        CSTParser.defines_macro(x) ||
            typof(x) === CSTParser.For ||
            typof(x) === CSTParser.While ||
            typof(x) === CSTParser.Let ||
            typof(x) === CSTParser.Generator || # and Flatten?
            typof(x) === CSTParser.Try ||
            typof(x) === CSTParser.Do ||
            CSTParser.defines_module(x) ||
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

"""
    scopes(x::EXPR, state)

Called when traversing the syntax tree and handles the association of
scopes with expressions. On the first pass this will add scopes as
necessary, on following passes it empties it. 
"""
function scopes(x::EXPR, state)
    clear_scope(x)
    if scopeof(x) === nothing && introduces_scope(x, state)
        setscope!(x, Scope(x))
    end
    s0 = state.scope
    if typof(x) === CSTParser.FileH
        setscope!(x, state.scope)
    elseif scopeof(x) isa Scope
        scopeof(x) != s0 && setparent!(scopeof(x), s0)
        state.scope = scopeof(x)
        if typof(x) === CSTParser.ModuleH # Add default modules to a new module
            state.scope.modules = Dict{Symbol,Any}()
            state.scope.modules[:Base] = getsymbolserver(state.server)[:Base]
            state.scope.modules[:Core] = getsymbolserver(state.server)[:Core]
        elseif typof(x) === CSTParser.BareModule
            state.scope.modules = Dict{String,Any}()
            state.scope.modules[:Core] = getsymbolserver(state.server)[:Core]
        end
        if CSTParser.defines_module(x) && bindingof(x) !== nothing # Add reference to out of scope binding (i.e. itself)
            # state.scope.names[bindingof(x).name] = bindingof(x)
            # TODO: move this to the binding stage
            add_binding(x, state)
        elseif typof(x) === CSTParser.Flatten && typof(x[1]) === CSTParser.Generator && length(x[1]) > 0 && typof(x[1][1]) === CSTParser.Generator
            setscope!(x[1][1], nothing)
        end
    end
    return s0
end