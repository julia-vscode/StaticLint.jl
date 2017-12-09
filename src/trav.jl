function trav(x::CSTParser.LeafNode, s, S::State)
    if x isa CSTParser.IDENTIFIER && !S.isquotenode
        binding = find_ref(CSTParser.str_value(x), S)
        push!(S.refs, Reference(x, binding, Location(S.loc.path, S.loc.offset + x.span)))
    end
    S.loc.offset += x.fullspan
end

function trav(x::CSTParser.EXPR{CSTParser.MacroName}, s, S::State)
    S.loc.offset += x.fullspan
end

# function trav(x::CSTParser.EXPR{CSTParser.MacroCall}, s, S::State)
#     S.loc.offset += x.fullspan
# end

function trav(x, s, S::State)
    x isa CSTParser.EXPR{CSTParser.Quotenode} && (S.isquotenode = true)
    for a in x
        get_external_binding(a, s, S)
        create_scope(a, s, S)
        lint_call(a, s, S)
        get_imports(a, S)
        trav(a, S.current_scope, S)
        S.current_scope = s
    end
    x isa CSTParser.EXPR{CSTParser.Quotenode} && (S.isquotenode = false)
    s
end

function trav(x)
    S = State()
    trav(x, S.current_scope, S)
    find_bad_refs(S)
    return S
end

function trav(path::String)
    S = State{FileSystem}(Scope(), Location(path, 0), [], [], 0:0, false, Dict(path => File(path, nothing, [])))
    x = CSTParser.parse(readstring(path), true)
    trav(x, S.current_scope, S)
    find_bad_refs(S)
    return S
end
