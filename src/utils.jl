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
    if hasref(x) && refof(x) isa Binding && refof(x).refs isa Vector
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
        x.meta.binding = nothing
    end
end
function clear_scope(x::EXPR)
    if hasmeta(x) && scopeof(x) isa Scope
        setparent!(scopeof(x), nothing)
        empty!(scopeof(x).names)
        if typof(x) === FileH && scopeof(x).modules isa Dict && haskey(scopeof(x).modules, "Base") && haskey(scopeof(x).modules, "Core")
            m1 = scopeof(x).modules["Base"]
            m2 = scopeof(x).modules["Core"]
            empty!(scopeof(x).modules)
            scopeof(x).modules["Base"] = m1
            scopeof(x).modules["Core"] = m2
        else
            scopeof(x).modules = nothing
        end
    end
end

function clear_ref(x::EXPR)
    if refof(x) isa Binding
        if refof(x).refs isa Vector
            for i in 1:length(refof(x).refs)
                if refof(x).refs[i] == x
                    deleteat!(refof(x).refs, i)
                    break
                end
            end
        end
        setref!(x, nothing)
    elseif refof(x) !== nothing
        setref!(x, nothing)
    end
end
function clear_error(x::EXPR)
    if hasmeta(x) && x.meta.error !== nothing 
        x.meta.error = nothing
    end
end
function clear_meta(x::EXPR)
    clear_binding(x)
    clear_ref(x)
    clear_scope(x)
    clear_error(x)
    if x.args !== nothing
        for a in x.args
            clear_meta(a)
        end
    end
end

function get_root_method(b, server)
    return b
end

function get_root_method(b::Binding, server, b1 = nothing, visited_bindings = Binding[])
    if b.prev === nothing || b == b.prev || !(b.prev isa Binding) || b in visited_bindings
        return b
    end
    push!(visited_bindings, b)
    if b.type == b.prev.type == CoreTypes.Function
        return get_root_method(b.prev, server, b, visited_bindings)
    elseif b.type == CoreTypes.Function && b.prev.type == CoreTypes.DataType
        return b.prev
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
    if scopeof(x) !== nothing
        return scopeof(x)
    elseif parentof(x) isa EXPR
        return retrieve_scope(parentof(x))
    end
    return 
end


function find_return_statements(x::EXPR)
    rets = EXPR[]
    if CSTParser.defines_function(x)
        find_return_statements(x.args[3], true, rets)
    end
    return rets
end

function find_return_statements(x::EXPR, last_stmt, rets)
    if last_stmt && !(typof(x) === CSTParser.Block || typof(x) === CSTParser.If || typof(x) === CSTParser.KEYWORD)
        push!(rets, x)
        return rets, false
    end 

    if typof(x) === CSTParser.Return
        push!(rets, x)
        return rets, true
    end


    if x.args isa Vector{EXPR}
        for i = 1:length(x.args)
            _, stop_iter = find_return_statements(x.args[i], last_stmt && (i == length(x.args) || (typof(x) === CSTParser.If && typof(x.args[i]) === CSTParser.Block)), rets)
            stop_iter && break
        end
    end
    return rets, false
end


function _expr_assert(x::EXPR, typ, nargs)
    typof(x) == typ && x.args isa Vector{EXPR} && length(x.args) == nargs
end

function _binary_assert(x, kind)
    typof(x) === CSTParser.BinaryOpCall && x.args isa Vector{EXPR} && length(x.args) == 3 && typof(x.args[2]) === CSTParser.OPERATOR && kindof(x.args[2]) === kind
end
    
# should only be called on Bindings to functions
function last_method(func::Binding)
    if func.next isa Binding && (func.next.type === CoreTypes.Function || (func.next.type === CoreTypes.DataType && func.type === CoreTypes.Function))
        return func.next
    else
        return func
    end
end

function prev_method(func::Binding)
    if func.prev isa Binding
        if func.prev.type === CoreTypes.Function
            return func.prev
        elseif func.prev.type === CoreTypes.DataType && func.prev.val isa EXPR && CSTParser.defines_struct(func.prev.val)
            return func.prev
        elseif (func.prev.val isa SymbolServer.FunctionStore || func.prev.val isa SymbolServer.DataTypeStore) && length(func.prev.val.methods) > 0
            return func.prev.val, 1
        end
    elseif (func.prev isa SymbolServer.FunctionStore || func.prev isa SymbolServer.DataTypeStore) && length(func.prev.methods) > 0
        return func.prev, 1
    end
    return nothing
end

function prev_method(func_iter::Tuple{T,Int}) where T <: Union{SymbolServer.FunctionStore,SymbolServer.DataTypeStore}
    func = func_iter[1]
    iter = func_iter[2]
    if iter < length(func.methods) 
        return func, iter + 1
    else
        return nothing
    end
end

function find_exported_names(x::EXPR)
    exported_vars = EXPR[]
    for i in 1:length(x.args[3].args)
        expr = x.args[3].args[i]
        if typof(expr) == CSTParser.Export && 
            for j = 2:length(expr)
                if CSTParser.isidentifier(expr.args[j]) && StaticLint.hasref(expr.args[j])
                    push!(exported_vars, expr.args[j])
                end
            end
        end
    end
    return exported_vars
end

"""
    is_in_fexpr(x::EXPR, f)
Check whether `x` isa the child of an expression for which `f(parent) == true`.
"""
function is_in_fexpr(x::EXPR, f)
    if f(x)
        return true
    elseif parentof(x) isa EXPR
        return is_in_fexpr(parentof(x), f)
    else
        return false
    end
end

"""
    get_in_fexpr(x::EXPR, f)
Get the `parent` of `x` for which `f(parent) == true`. (is_in_fexpr should be called first.)
"""
function get_parent_fexpr(x::EXPR, f)
    if f(x)
        return x
    elseif parentof(x) isa EXPR
        return get_parent_fexpr(parentof(x), f)
    end
end

hasreadperm(p::String) = (uperm(p) & 0x04) == 0x04

# check whether a path is in (including subfolders) the julia base dir. Returns "" if not, and the path to the base dir if so.
function _is_in_basedir(path::AbstractString)
    i = findfirst(r".*base", path)
    i == nothing && return ""
    path1 = path[i]
    !hasreadperm(path1) && return ""
    !isdir(path1) && return ""
    files = readdir(path1)
    if all(f -> f in files, ["Base.jl", "coreio.jl", "essentials.jl", "exports.jl"])
        return path1
    end
end
