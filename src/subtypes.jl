function _issubtype(a, b, store)
    _isany(b) && return true
    _type_compare(a, b) && return true
    sup_a = _super(a, store)
    _type_compare(sup_a, b) && return true    
    !_isany(sup_a) && return _issubtype(sup_a, b, store)
    return false
end

_isany(x::SymbolServer.DataTypeStore) = x.name.name == VarRef(VarRef(nothing, :Core), :Any)
_isany(x) = false

_type_compare(a::SymbolServer.DataTypeStore, b::SymbolServer.DataTypeStore) = a.name == b.name
_type_compare(a, b) = a == b

function _super(a::SymbolServer.DataTypeStore, store)
    SymbolServer._lookup(a.super.name, store)
end

function _super(b::Binding, store)
    StaticLint.CoreTypes.isdatatype(b.type) || error()
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
