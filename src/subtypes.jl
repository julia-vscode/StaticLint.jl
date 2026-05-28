function _issubtype(a, b, store)
    _isany(b) && return true
    _type_compare(a, b) && return true
    sup_a = _super(a, store)
    _type_compare(sup_a, b) && return true
    !_isany(sup_a) && return _issubtype(sup_a, b, store)
    return false
end

function _has_type_intersection(a, b, store)
    return _issubtype(a, b, store) || _issubtype(b, a, store)
end

_isany(x::SymbolServer.FakeTypeName) = x.name == VarRef(VarRef(nothing, :Core), :Any)
_isany(x::SymbolServer.DataTypeStore) = x.name.name == VarRef(VarRef(nothing, :Core), :Any)
_isany(x) = false

_type_compare(a::SymbolServer.DataTypeStore, b::SymbolServer.DataTypeStore) = a.name == b.name
_type_compare(a::SymbolServer.FakeTypeName, b::SymbolServer.FakeTypeName) = a == b
_type_compare(a::SymbolServer.FakeTypeName, b::SymbolServer.DataTypeStore) = a == b.name
_type_compare(a::SymbolServer.DataTypeStore, b::SymbolServer.FakeTypeName) = a.name == b
_type_compare(a::SymbolServer.DataTypeStore, b::SymbolServer.FakeUnion) = _type_compare(a, b.a) || _type_compare(a, b.b)

_type_compare(a::SymbolServer.DataTypeStore, b::SymbolServer.FakeTypeVar) = _type_compare(a, b.ub)

# When matching against a `FakeUnionAll`, the type's parameters get
# hoisted into UnionAll vars and the inner `FakeTypeName` ends up with
# empty `.parameters`. Compare base name VarRefs only so e.g.
# `Array{T,N}` still intersects with `AbstractArray where N where T`.
_unionall_basename(x::SymbolServer.FakeUnionAll) =
    x.body isa SymbolServer.FakeUnionAll ? _unionall_basename(x.body) : x.body
_basename(x::SymbolServer.FakeTypeName) = x.name
_basename(x::SymbolServer.DataTypeStore) = x.name.name
_basename(_) = nothing

function _type_compare(a::SymbolServer.DataTypeStore, b::SymbolServer.FakeUnionAll)
    inner = _unionall_basename(b)
    bn = _basename(inner)
    bn === nothing ? _type_compare(a, inner) : a.name.name == bn
end
function _type_compare(a::SymbolServer.FakeUnionAll, b::SymbolServer.DataTypeStore)
    inner = _unionall_basename(a)
    bn = _basename(inner)
    bn === nothing ? _type_compare(inner, b) : bn == b.name.name
end
function _type_compare(a::SymbolServer.FakeTypeName, b::SymbolServer.FakeUnionAll)
    inner = _unionall_basename(b)
    bn = _basename(inner)
    bn === nothing ? _type_compare(a, inner) : a.name == bn
end
function _type_compare(a::SymbolServer.FakeUnionAll, b::SymbolServer.FakeTypeName)
    inner = _unionall_basename(a)
    bn = _basename(inner)
    bn === nothing ? _type_compare(inner, b) : bn == b.name
end

_type_compare(a, b) = a == b

_super(a::SymbolServer.DataTypeStore, store) = SymbolServer._lookup(a.super.name, store)
_super(a::SymbolServer.FakeTypeVar, _) = a.ub
_super(a::SymbolServer.FakeUnionAll, _) = a.body
_super(a::SymbolServer.FakeTypeName, store) = _super(SymbolServer._lookup(a.name, store), store)
_super(::SymbolServer.FakeUnion, store) = CoreTypes.Any
_super(::SymbolServer.FakeTypeofBottom, store) = CoreTypes.Any
@static if !(Vararg isa Type)
    _super(a::SymbolServer.FakeTypeofVararg, _) = CoreTypes.Any
end
_super(_, _) = CoreTypes.Any

function _super(b::Binding, store)
    StaticLint.CoreTypes.isdatatype(b.type) || return store[:Core][:Any]
    b.val isa Binding && return _super(b.val, store)
    sup = _super(b.val, store)
    if sup isa EXPR && StaticLint.hasref(sup)
        StaticLint.refof(sup)
    else
        store[:Core][:Any]
    end
end

function _super(x::EXPR, store)::Union{EXPR,Nothing}
    if x.head === :struct
        _super(x.args[2], store)
    elseif x.head === :abstract || x.head === :primtive
        _super(x.args[1], store)
    elseif CSTParser.issubtypedecl(x)
        x.args[2]
    elseif CSTParser.isbracketed(x)
        _super(x.args[1], store)
    end
end

function subtypes(T::Binding)
    @assert CSTParser.defines_abstract(T.val)
    subTs = []
    for r in T.refs
        if r isa EXPR && r.parent isa EXPR && CSTParser.issubtypedecl(r.parent) && r.parent.parent isa EXPR && CSTParser.defines_datatype(r.parent.parent)
            push!(subTs, r.parent.parent)
        end
    end
    subTs
end
