quoted(x) = x.typ === Quote || x.typ === Quotenode
unquoted(x) = x.typ === UnaryOpCall && x.args[1].typ === OPERATOR && x.args[1].kind == CSTParser.Tokens.EX_OR

function get_ids(x, q = false, ids = [])
    if quoted(x)
        q = true
    end
    if q && unquoted(x)
        q = false
    end
    if isidentifier(x) 
        !q && push!(ids, x)
    elseif x.args isa Vector
        for a in x.args
            get_ids(a, q, ids)
        end
    end
    ids
end

function collect_bindings_refs(x::EXPR, bindings = [], refs = [])
    if x.binding !== nothing
        push!(bindings, x)
    end
    if StaticLint.hasref(x)
        push!(refs, x)
    end
    if x.args !== nothing
        for a in x.args
            collect_bindings_refs(a, bindings, refs)
        end
    end
    return bindings, refs
end

function remove_ref(x::EXPR)
    if hasref(x) && x.ref isa Binding
        for ia in enumerate(x.ref.refs)
            if ia[2] == x
                deleteat!(x.ref.refs, ia[1])
                x.ref = nothing
                return
            end
        end
        error()
    end
end

function remove_binding(x::EXPR)
    if x.binding isa Binding
        
    end
end