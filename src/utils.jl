quoted(x) = typof(x) === Quote || typof(x) === Quotenode
unquoted(x) = typof(x) === UnaryOpCall && typof(x.args[1]) === OPERATOR && kindof(x.args[1]) == CSTParser.Tokens.EX_OR

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
    if bindingof(x) !== nothing
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
    if hasref(x) && refof(x) isa Binding
        for ia in enumerate(refof(x).refs)
            if ia[2] == x
                deleteat!(refof(x).refs, ia[1])
                setref!(x, nothing)
                return
            end
        end
        error()
    end
end

function clear_binding(x::EXPR)
    if bindingof(x) isa Binding
        for r in bindingof(x).refs
            if r isa EXPR
                setref!(r, nothing)
            elseif r isa Binding
                clear_binding(r)
            end
        end
        x.binding = nothing
    end
end
function clear_scope(x::EXPR)
    if x.scope isa Scope
        setparent!(x.scope, nothing)
        empty!(x.scope.names)
        if typof(x) === FileH && x.scope.modules isa Dict && haskey(x.scope.modules, "Base") && haskey(x.scope.modules, "Core")
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
    if refof(x) isa Binding
        for i in 1:length(refof(x).refs)
            if refof(x).refs[i] == x
                deleteat!(refof(x).refs, i)
                break
            end
        end
        setref!(x, nothing)
    elseif refof(x) !== nothing
        setref!(x, nothing)
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

function retrieve_delayed_scope(x)
    if (CSTParser.defines_function(x) || CSTParser.defines_macro(x)) && scopeof(x) !== nothing
        if parentof(scopeof(x)) !== nothing
            return parentof(scopeof(x))
        else
            return scopeof(x)
        end
    elseif typof(x) === Export
        return retrieve_scope(x)
    elseif parentof(x) !== nothing
        return retrieve_delayed_scope(parentof(x))
    end
    return nothing
end

function retrieve_scope(x)
    if scopeof(x) != nothing
        return scopeof(x)
    elseif parentof(x) isa EXPR
        return retrieve_scope(parentof(x))
    end
    return 
end
