quoted(x) = headof(x) === :quote || headof(x) === :quotenode
unquoted(x) = isunarycall(x) && valof(x.args[1]) == "\$"

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
        if headof(x) === :file && scopeof(x).modules isa Dict && scopehasmodule(scopeof(x), :Base) && scopehasmodule(scopeof(x), :Core)
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
    if x.args !== nothing
        for a in x.args
            clear_meta(a)
        end
    end
    # if x.trivia !== nothing
    #     for a in x.trivia
    #         clear_meta(a)
    #     end
    # end
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


# function find_return_statements(x::EXPR)
#     rets = EXPR[]
#     if CSTParser.defines_function(x)
#         find_return_statements(x.args[2], true, rets)
#     end
#     return rets
# end

# function find_return_statements(x::EXPR, last_stmt, rets)
#     if last_stmt && !(headof(x) === :block || headof(x) === :if || iskw(x))
#         push!(rets, x)
#         return rets, false
#     end

#     if headof(x) === :return
#         push!(rets, x)
#         return rets, true
#     end


#     for i = 1:length(x)
#         _, stop_iter = find_return_statements(x[i], last_stmt && (i == length(x) || (headof(x) === CSTParser.If && headof(x[i]) === CSTParser.Block)), rets)
#         stop_iter && break
#     end
#     return rets, false
# end

last_method(b::Binding, visited = Binding[]) = b.next isa Binding && b.next.type === CoreTypes.Function && !(b in visited) ? (push!(visited, b);last_method(b.next, visited)) : b

function find_exported_names(x::EXPR)
    exported_vars = EXPR[]
    for i in 1:length(x.args[3].args)
        expr = x.args[3].args[i]
        if headof(expr) === :export
            for j = 2:length(expr.args)
                if isidentifier(expr.args[j]) && hasref(expr.args[j])
                    push!(exported_vars, expr.args[j])
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
    if all(f->f in files, ["Base.jl", "coreio.jl", "essentials.jl", "exports.jl"])
        return path1
    end
    return ""
end

isexportedby(k::Symbol, m::SymbolServer.ModuleStore) = haskey(m, k) && k in m.exportednames
isexportedby(k::String, m::SymbolServer.ModuleStore) = isexportedby(Symbol(k), m)
isexportedby(x::EXPR, m::SymbolServer.ModuleStore) = isexportedby(valof(x), m)
isexportedby(k, m::SymbolServer.ModuleStore) = false

function retrieve_toplevel_scope(x::EXPR)
    if scopeof(x) !== nothing && (CSTParser.defines_module(x) || headof(x) === :file)
        return scopeof(x)
    elseif parentof(x) isa EXPR
        return retrieve_toplevel_scope(parentof(x))
    else
        @info "Tried to reach toplevel scope, no scope found. Final expression $(headof(x))"
        return nothing
    end
end
retrieve_toplevel_scope(s::Scope) = (CSTParser.defines_module(s.expr) || headof(s.expr) === :file || !(parentof(s) isa Scope)) ? s : retrieve_toplevel_scope(parentof(s))


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
    if CSTParser.iswhere(p) || CSTParser.isdeclaration(p)
        return issigoffuncdecl(parentof(p))
    elseif CSTParser.defines_function(p)
        return true
    else
        return false
    end
end
issigoffuncdecl(x::EXPR, p) = false
