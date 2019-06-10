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
    elseif x.args !== nothing
        for i in 1:length(x.args)
            get_ids(x.args[i], q, ids)
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

function clear_binding(x::EXPR)
    if x.binding isa Binding
        for r in x.binding.refs
            if r isa EXPR
                r.ref = nothing
            elseif r isa Binding
                clear_binding(r)
            end
        end
        x.binding = nothing
    end
end
function clear_scope(x::EXPR)
    if x.scope isa Scope
        x.scope.parent = nothing
        empty!(x.scope.names)
        if x.typ === FileH && x.scope.modules isa Dict && haskey(x.scope.modules, "Base") && haskey(x.scope.modules, "Core")
            m1 = x.scope.modules["Base"]
            m2 = x.scope.modules["Core"]
            empty!(x.scope.modules)
            x.scope.modules["Base"] = m1
            x.scope.modules["Core"] = m2
        else
            x.scope.modules = nothing
        end
    end
end

function clear_ref(x::EXPR)
    if x.ref isa Binding
        for i in 1:length(x.ref.refs)
            if x.ref.refs[i] == x
                deleteat!(x.ref.refs, i)
                break
            end
        end
        x.ref = nothing
    elseif x.ref !== nothing
        x.ref = nothing
    end
end
function clear_meta(x::EXPR)
    clear_binding(x)
    clear_ref(x)
    clear_scope(x)
    if x.args !== nothing
        for a in x.args
            clear_meta(a)
        end
    end
end



function get_root_method(b, server)
    return b
end

function get_root_method(b::Binding, server, b1 = nothing, bs = Binding[])
    if b.overwrites === nothing || b == b.overwrites || !(b.overwrites isa Binding)
        return b
    elseif b.overwrites.t == getsymbolserver(server)["Core"].vals["Function"]
        return get_root_method(b.overwrites, server, b, bs)
    elseif b.overwrites.t == getsymbolserver(server)["Core"].vals["DataType"]
        return b.overwrites
    else
        return b
    end
end
