quoted(x) = typof(x) === Quote || typof(x) === Quotenode
unquoted(x) = is_unary_call(x) && isoperator(x[1]) && kindof(x[1]) == CSTParser.Tokens.EX_OR

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
        if typof(x) === CSTParser.FileH && scopeof(x).modules isa Dict && scopehasmodule(scopeof(x), :Base) && scopehasmodule(scopeof(x), :Core)
            m1, m2 = getscopemodule(scopeof(x), :Base), getscopemodule(scopeof(x), :Core)
            empty!(scopeof(x).modules)
            addmoduletoscope!(scopeof(x), m1)
            addmoduletoscope!(scopeof(x), m2)
        else
            scopeof(x).modules = nothing
        end
        if scopeof(x).overloaded !== nothing
            empty!(scopeof(x).overloaded)
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
    for a in x
        clear_meta(a)
    end
end

function get_root_method(b, server)
    return b
end

function get_root_method(b::Binding, server, b1=nothing, visited_bindings=Binding[])
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
    else
        return retrieve_scope(x)
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
        find_return_statements(x[3], true, rets)
    end
    return rets
end

function find_return_statements(x::EXPR, last_stmt, rets)
    if last_stmt && !(typof(x) === CSTParser.Block || typof(x) === CSTParser.If || iskw(x))
        push!(rets, x)
        return rets, false
    end

    if typof(x) === CSTParser.Return
        push!(rets, x)
        return rets, true
    end


    for i = 1:length(x)
        _, stop_iter = find_return_statements(x[i], last_stmt && (i == length(x) || (typof(x) === CSTParser.If && typof(x[i]) === CSTParser.Block)), rets)
        stop_iter && break
    end
    return rets, false
end

last_method(b::Binding, visited=Binding[]) = b.next isa Binding && b.next.type === CoreTypes.Function && !(b in visited) ? (push!(visited, b);last_method(b.next, visited)) : b

function find_exported_names(x::EXPR)
    exported_vars = EXPR[]
    for i in 1:length(x[3])
        expr = x[3][i]
        if typof(expr) == CSTParser.Export &&
            for j = 2:length(expr)
                if isidentifier(expr[j]) && hasref(expr[j])
                    push!(exported_vars, expr[j])
                end
            end
        end
    end
    return exported_vars
end

hasreadperm(p::String) = (uperm(p) & 0x04) == 0x04

# check whether a path is in (including subfolders) the julia base dir. Returns "" if not, and the path to the base dir if so.
function _is_in_basedir(path::String)
    i = findfirst(r".*base", path)
    i === nothing && return ""
    path1 = path[i]::String
    !hasreadperm(path1) && return ""
    !isdir(path1) && return ""
    files = readdir(path1)
    if all(f -> f in files, ["Base.jl", "coreio.jl", "essentials.jl", "exports.jl"])
        return path1
    end
    return ""
end

isexportedby(k::Symbol, m::SymbolServer.ModuleStore) = haskey(m, k) && k in m.exportednames
isexportedby(k::String, m::SymbolServer.ModuleStore) = isexportedby(Symbol(k), m)
isexportedby(x::EXPR, m::SymbolServer.ModuleStore) = isexportedby(valof(x), m)
isexportedby(k, m::SymbolServer.ModuleStore) = false

function retrieve_toplevel_scope(x::EXPR)
    if scopeof(x) !== nothing && (CSTParser.defines_module(x) || typof(x) === CSTParser.FileH)
        return scopeof(x)
    elseif parentof(x) isa EXPR
        return retrieve_toplevel_scope(parentof(x))
    else
        @info "Tried to reach toplevel scope, no scope found. Final expression $(typof(x))"
        return nothing
    end
end
retrieve_toplevel_scope(s::Scope) = (CSTParser.defines_module(s.expr) || typof(s.expr) === CSTParser.FileH || !(parentof(s) isa Scope)) ? s : retrieve_toplevel_scope(parentof(s))


# b::SymbolServer.FunctionStore or DataTypeStore
# tls is a top-level Scope (expected to contain loaded modules)
# for a FunctionStore b, checks whether additional methods are provided by other packages
# f is a function that returns `true` if we want to break early from the loop

iterate_over_ss_methods(b, tls, server, f) = false
function iterate_over_ss_methods(b::SymbolServer.FunctionStore, tls::Scope, server, f)
    for m in b.methods
        ret = f(m)
        ret && return true
    end
    if b.extends in keys(getsymbolextendeds(server)) && tls.modules !== nothing
        # above should be modified,
        rootmod = SymbolServer._lookup(b.extends.parent, getsymbolserver(server)) # points to the module containing the initial function declaration
        if rootmod !== nothing && haskey(rootmod, b.extends.name) # check rootmod exists, and that it has the variable
            rootfunc = rootmod[b.extends.name]
            # find extensoions
            if haskey(getsymbolextendeds(server), b.extends) # method extensions listed
                for vr in getsymbolextendeds(server)[b.extends] # iterate over packages with extensions
                    !(SymbolServer.get_top_module(vr) in keys(tls.modules)) && continue
                    rootmod = SymbolServer._lookup(vr, getsymbolserver(server))
                    !(rootmod isa SymbolServer.ModuleStore) && continue
                    if haskey(rootmod.vals, b.extends.name) && (rootmod.vals[b.extends.name] isa SymbolServer.FunctionStore || rootmod.vals[b.extends.name] isa SymbolServer.DataTypeStore)# check package is available and has ref
                        for m in rootmod.vals[b.extends.name].methods #
                            ret = f(m)
                            ret && return true
                        end
                    end
                end
            end
        end
    end
    return false
end

function iterate_over_ss_methods(b::SymbolServer.DataTypeStore, tls::Scope, server, f)
    if b.name isa SymbolServer.VarRef
        bname = b.name
    elseif b.name isa SymbolServer.FakeTypeName
        bname = b.name.name
    end
    for m in b.methods
        ret = f(m)
        ret && return true
    end
    if (bname in keys(getsymbolextendeds(server))) && tls.modules !== nothing
        # above should be modified,
        rootmod = SymbolServer._lookup(bname.parent, getsymbolserver(server), true) # points to the module containing the initial function declaration
        if rootmod !== nothing && haskey(rootmod, bname.name) # check rootmod exists, and that it has the variable
            rootfunc = rootmod[bname.name]
            # find extensoions
            if haskey(getsymbolextendeds(server), bname) # method extensions listed
                for vr in getsymbolextendeds(server)[bname] # iterate over packages with extensions
                    !(SymbolServer.get_top_module(vr) in keys(tls.modules)) && continue
                    rootmod = SymbolServer._lookup(vr, getsymbolserver(server))
                    !(rootmod isa SymbolServer.ModuleStore) && continue
                    if haskey(rootmod.vals, bname.name) && (rootmod.vals[bname.name] isa SymbolServer.FunctionStore || rootmod.vals[bname.name] isa SymbolServer.DataTypeStore)# check package is available and has ref
                        for m in rootmod.vals[bname.name].methods #
                            ret = f(m)
                            ret && return true
                        end
                    end
                end
            end
        end
    end
    return false
end

# CST utils
fcall_name(x::EXPR) = is_call(x) && length(x) > 0 && valof(x[1])
is_call(x::EXPR) = typof(x) === CSTParser.Call
is_unary_call(x::EXPR) = typof(x) === CSTParser.UnaryOpCall && length(x) == 2
is_binary_call(x::EXPR) = typof(x) === CSTParser.BinaryOpCall && length(x) == 3
is_binary_call(x::EXPR, opkind) = is_binary_call(x) && kindof(x[2]) === opkind
is_macro_call(x::EXPR) = typof(x) === CSTParser.MacroCall
is_macroname(x::EXPR) = (typof(x) === CSTParser.MacroName && length(x) == 2) || (is_getfield_w_quotenode(x) && is_macroname(x[3][1]))
is_id_or_macroname(x::EXPR) = isidentifier(x) || is_macroname(x)
is_getfield(x) = x isa EXPR && is_binary_call(x) && kindof(x[2]) == CSTParser.Tokens.DOT
is_getfield_w_quotenode(x) = x isa EXPR && is_binary_call(x) && kindof(x[2]) == CSTParser.Tokens.DOT && typof(x[3]) === CSTParser.Quotenode && length(x[3]) > 0
is_declaration(x::EXPR) = is_binary_call(x) && kindof(x[2]) === CSTParser.Tokens.DECLARATION
is_where(x::EXPR) = typof(x) === CSTParser.WhereOpCall
isnonstdid(x::EXPR) = typof(x) === CSTParser.NONSTDIDENTIFIER
is_kwarg(x::EXPR) = typof(x) === CSTParser.Kw
is_parameters(x::EXPR) = typof(x) === CSTParser.Parameters
is_tuple(x::EXPR) = typof(x) === CSTParser.TupleH
is_curly(x::EXPR) = typof(x) === CSTParser.Curly
is_invis_brackets(x::EXPR) = typof(x) === CSTParser.InvisBrackets
iswherecall(x::EXPR) = typof(x) === CSTParser.WhereOpCall
rem_wheres(x::EXPR) = iswherecall(x) ? rem_wheres(x[1]) : x
rem_wheres_decls(x::EXPR) = iswherecall(x) || CSTParser.isdeclaration(x) ? rem_wheres_decls(x[1]) : x
hasparent(x::EXPR) = parentof(x) isa EXPR


"""
    is_in_fexpr(x::EXPR, f)
Check whether `x` isa the child of an expression for which `f(parent) == true`.
"""
is_in_fexpr(x::EXPR, f) = f(x) || (parentof(x) isa EXPR && is_in_fexpr(parentof(x), f))

"""
    get_in_fexpr(x::EXPR, f)
Get the `parent` of `x` for which `f(parent) == true`. (is_in_fexpr should be called first.)
"""
get_parent_fexpr(x::EXPR, f) = f(x) ? x : get_parent_fexpr(parentof(x), f)

issigoffuncdecl(x::EXPR) = parentof(x) isa EXPR ? issigoffuncdecl(x, parentof(x)) : false
function issigoffuncdecl(x::EXPR, p::EXPR)
    if CSTParser.is_where(p) || CSTParser.isdeclaration(p)
        return issigoffuncdecl(parentof(p))
    elseif CSTParser.defines_function(p)
        return true
    else
        return false
    end
end
issigoffuncdecl(x::EXPR, p) = false
