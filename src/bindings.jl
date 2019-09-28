mutable struct Binding
    name::EXPR
    val::Union{EXPR,SymbolServer.SymStore,Nothing}
    type::Union{EXPR,SymbolServer.SymStore,Nothing}
    refs
    prev::Union{Binding,SymbolServer.SymStore,Nothing}
    next::Union{Binding,SymbolServer.SymStore,Nothing}
end
Binding(x::EXPR) = Binding(CSTParser.get_name(x), x, nothing, nothing, nothing, nothing)

mutable struct Scope
    parent::Union{Scope,Nothing}
    expr::EXPR
    names::Dict{String,Binding}
    modules::Union{Nothing,Dict{String,Any}}
    ismodule::Bool
end
Scope(expr) = Scope(nothing, expr, Dict{String,Binding}(), nothing, false)
function introduces_scope(x::EXPR, state)
    if typof(x) === CSTParser.BinaryOpCall
        if kindof(x.args[2]) === CSTParser.Tokens.EQ && CSTParser.is_func_call(x.args[1])
            return true
        elseif kindof(x.args[2]) === CSTParser.Tokens.EQ && typof(x.args[1]) === CSTParser.Curly
            return true
        elseif kindof(x.args[2]) === CSTParser.Tokens.ANON_FUNC
            return true
        end
    elseif typof(x) === CSTParser.WhereOpCall
        #unless in func def signature
        return true
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
end


mutable struct Meta
    binding::Union{Nothing,Binding}
    scope::Union{Nothing,Scope}
    ref::Union{Nothing,Binding,SymbolServer.SymStore}
    error
end
Meta() = Meta(nothing, nothing, nothing, nothing)
function Base.show(io::IO, m::Meta)
    m.binding !== nothing && printstyled(io, " $(Expr(m.binding.name))", m.binding.type === nothing ? "" : "::", color = :blue)
    m.ref !== nothing && printstyled(io, " * ", color = :red)
    m.scope !== nothing && printstyled(io, " new scope", color = :green)
end

hasmeta(x::EXPR) = x.meta isa Meta

hasbinding(m::Meta) = m.binding isa Binding
hasbinding(x::EXPR) = hasmeta(x) && hasbinding(x.meta)
bindingof(x::EXPR) = x.meta.binding

hasscope(m::Meta) = m.scope isa Scope
hasscope(x::EXPR) = hasmeta(x) && hasscope(x.meta)
scopeof(x::EXPR) = x.meta.scope

hasref(m::Meta) = m.ref !== nothing
hasref(x::EXPR) = hasmeta(x) && hasref(x.meta)
refof(x::EXPR) = x.meta.ref

function setscope!(x::EXPR, s::Scope)
    if !hasmeta(x)
        x.meta = Meta()
    end
    x.meta.scope = s
end

function mark_binding!(x, state)
    if hasbinding(x)
        return
    end
    if !hasmeta(x)
        x.meta = Meta()
    end
    if typof(x) === ModuleH || typof(x) === BareModule
        x.meta.binding = Binding(x.args[2], x, getsymbolserver(state.server)["Core"].vals["Module"], [], nothing, nothing)
    elseif typof(x) === FunctionDef
        x.meta.binding = Binding(CSTParser.get_name(x), x, getsymbolserver(state.server)["Core"].vals["Function"], [], nothing, nothing)
    elseif typof(x) === Macro
        x.meta.binding = Binding(CSTParser.get_name(x), x, getsymbolserver(state.server)["Core"].vals["Function"], [], nothing, nothing)
    end
end
