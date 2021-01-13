mutable struct Binding
    name::EXPR
    val::Union{Binding,EXPR,SymbolServer.SymStore,Nothing}
    type::Union{Binding,EXPR,SymbolServer.SymStore,Nothing}
    refs::Vector{Any}
    prev::Union{Binding,SymbolServer.SymStore,Nothing}
    next::Union{Binding,SymbolServer.SymStore,Nothing}
end
Binding(x::EXPR) = Binding(CSTParser.get_name(x), x, nothing, [], nothing, nothing)

function Base.show(io::IO, b::Binding)
    printstyled(io, " Binding(", Expr(b.name),
        b.type === nothing ? "" : ":: ",
        b.refs isa Vector ? "($(length(b.refs)) refs))" : ")", color=:blue)
end


hasbinding(x::EXPR) = hasmeta(x) && hasbinding(x.meta)
bindingof(x) = nothing
bindingof(x::EXPR) = bindingof(x.meta)


hasref(x::EXPR) = hasmeta(x) && hasref(x.meta)
refof(x::EXPR) = hasmeta(x) ? x.meta.ref : nothing


function gotoobjectofref(x::EXPR)
    r = refof(x)
    if r isa SymbolServer.SymStore
        return r
    elseif r isa Binding

    end
end


# Note to self, check consistency of marking self-reference of bindings (i.e.
# for, `function f end` we resolve `f` to itself at this stage.)
function mark_bindings!(x::EXPR, state)
    if hasbinding(x)
        return
    end
    if !hasmeta(x)
        x.meta = Meta()
    end
    if isassignment(x)
        if CSTParser.is_func_call(x.args[1])
            name = CSTParser.get_name(x)
            mark_binding!(x)
            mark_sig_args!(x.args[1])
            if isidentifier(name)
                setref!(name, bindingof(x))
            end
        elseif CSTParser.iscurly(x.args[1])
            mark_typealias_bindings!(x)
        elseif !is_getfield(x.args[1])
            mark_binding!(x.args[1], x)
        end
    elseif CSTParser.defines_anon_function(x)
        mark_binding!(x.args[1], x)
    elseif CSTParser.iswhere(x)
        for i = 2:length(x.args)
            mark_binding!(x.args[i])
        end
    elseif headof(x) === :for
        markiterbinding!(x.args[2])
    elseif headof(x) === :generator 
        for i = 2:length(x.args)
            markiterbinding!(x.args[i])
        end
    elseif headof(x) === :filter
        for i = 2:length(x.args)
            markiterbinding!(x.args[i])
        end
    # elseif headof(x) === CSTParser.Flatten && length(x.args) === 1 && length(x[1]) >= 3 && length(x[1][1]) >= 3
    #     for i = 3:length(x[1][1])
    #         ispunctuation(x[1][1][i]) && continue
    #         markiterbinding!(x[1][1][i])
    #     end
    #     for i = 3:length(x[1])
    #         ispunctuation(x[1][i]) && continue
    #         markiterbinding!(x[1][i])
    #     end
    elseif headof(x) === :do
        if istuple(x.args[2])
            for i in 1:length(x.args[2].args)
                mark_binding!(x.args[2].args[i])
            end
        end
    elseif headof(x) === :function || headof(x) === :macro
        name = CSTParser.get_name(x)
        x.meta.binding = Binding(name, x, CoreTypes.Function, [], nothing, nothing)
        if isidentifier(name)
            setref!(name, bindingof(x))
        end
        mark_sig_args!(CSTParser.get_sig(x))
    elseif CSTParser.defines_module(x)
        x.meta.binding = Binding(x.args[2], x, CoreTypes.Module, [], nothing, nothing)
        setref!(x.args[2], bindingof(x))
    elseif headof(x) === :try && isidentifier(x.args[2])
        mark_binding!(x.args[2])
        setref!(x.args[2], bindingof(x.args[2]))
    elseif CSTParser.defines_datatype(x)
        name = CSTParser.get_name(x)
        x.meta.binding = Binding(name, x, CoreTypes.DataType, [], nothing, nothing)
        kwdef = parentof(x) isa EXPR && _points_to_Base_macro(parentof(x).args[1], Symbol("@kwdef"), state)
        if isidentifier(name)
            setref!(name, bindingof(x))
        end
        mark_parameters(CSTParser.get_sig(x))
        if CSTParser.defines_struct(x) # mark field block
            for i in 1:length(x.args[3].args)
                CSTParser.defines_function(x.args[3].args[i]) && continue
                arg = x.args[3].args[i]
                if kwdef && CSTParser.isassignment(arg)
                    arg = arg.args[1]
                end
                mark_binding!(arg)
            end
        end
    elseif headof(x) === :local
        for i = 1:length(x.args)
            if isidentifier(x.args[i])
                mark_binding!(x.args[i])
                setref!(x.args[i], bindingof(x.args[i]))
            end
        end
    end
end


function mark_binding!(x::EXPR, val=x)
    if CSTParser.iskwarg(x) || (CSTParser.isdeclaration(x) && CSTParser.istuple(x.args[1]))
        mark_binding!(x.args[1], x)
    elseif CSTParser.istuple(x) || CSTParser.isparameters(x)
        for arg in x.args
            mark_binding!(arg, val)
        end
    elseif CSTParser.isbracketed(x)
        mark_binding!(CSTParser.rem_invis(x), val)
    elseif CSTParser.issplat(x)
        mark_binding!(x.args[1], x)
    elseif !(isunarysyntax(x) && valof(headof(x)) == "::")
        if !hasmeta(x)
            x.meta = Meta()
        end
        x.meta.binding = Binding(CSTParser.get_name(x), val, nothing, [], nothing, nothing)
    end
    return x
end


function mark_parameters(sig::EXPR)
    signame = CSTParser.rem_where_subtype(sig)
    if CSTParser.iscurly(signame)
        for i = 2:length(signame.args)
            mark_binding!(signame.args[i])
        end
    end
    return sig
end


function markiterbinding!(iter::EXPR)
    if CSTParser.isassignment(iter)
        mark_binding!(iter.args[1], iter)
    elseif CSTParser.iscall(iter) && CSTParser.isoperator(iter.args[1]) && (valof(iter.args[1]) == "in" || valof(iter.args[1]) == "∈")
        mark_binding!(iter.args[2], iter)
    elseif headof(iter) === :block
        for i = 1:length(iter.args)
            markiterbinding!(iter.args[i])
        end
    end
    return iter
end

function mark_sig_args!(x::EXPR)
    if CSTParser.iscall(x) || CSTParser.istuple(x)
        if x.args !== nothing && length(x.args) > 0
            if CSTParser.isbracketed(x.args[1]) && length(x.args[1].args) > 0 && CSTParser.isdeclaration(x.args[1].args[1])
                mark_binding!(x.args[1].args[1])
            end
            for i = (CSTParser.iscall(x) ? 2 : 1):length(x.args)
                a = x.args[i]
                if CSTParser.isparameters(a)
                    for j = 1:length(a.args)
                        aa = a.args[j]
                        mark_binding!(aa)
                    end
                elseif CSTParser.ismacrocall(a) && CSTParser.isidentifier(a.args[1]) && valofid(a.args[1]) == "@nospecialize" && length(a.args) == 3
                    mark_binding!(a.args[3])
                else
                    mark_binding!(a)
                end
            end
        end
    elseif CSTParser.iswhere(x)
        for i in 1:length(x.args)
            mark_binding!(x.args[i])
        end
        mark_sig_args!(x.args[1])
    elseif CSTParser.isbracketed(x)
        mark_sig_args!(x.args[1])
    elseif CSTParser.isdeclaration(x)
        mark_sig_args!(x.args[1])
    elseif CSTParser.isbinarycall(x)
        mark_binding!(x.args[1])
        mark_binding!(x.args[2])
    elseif CSTParser.isunarycall(x) && length(x.args) == 2 && (CSTParser.isbracketed(x.args[2]) || CSTParser.isdeclaration(x.args[2]))
        mark_binding!(x.args[2])
    end
end

function mark_typealias_bindings!(x::EXPR)
    mark_binding!(x, x)
    setscope!(x, Scope(x))
    for i = 2:length(x.args[1].args)
        arg = x.args[1].args[i]
        if isidentifier(arg)
            mark_binding!(arg)
        elseif CSTParser.issubtypedecl(arg) && isidentifier(arg.args[1])
            mark_binding!(arg.args[1])
        end
    end
    return x
end

rem_wheres_decls(x) = (CSTParser.iswhere(x) || CSTParser.isdeclaration(x)) ? x.args[1] : x

function is_in_funcdef(x)
    if !(parentof(x) isa EXPR)
        return false
    elseif CSTParser.iswhere(parentof(x)) || CSTParser.isbracketed(parentof(x))
        return is_in_funcdef(parentof(x))
    elseif headof(parentof(x)) === :function || CSTParser.isassignment(parentof(x))
        return true
    else
        return false
    end
end

function _in_func_def(x::EXPR)
    # only called in :where
    # check 1st arg contains a call (or op call)
    ex = rem_wheres_decls(x.args[1])

    !(CSTParser.iscall(ex) || CSTParser.is_getfield(ex) || CSTParser.isunarycall(ex)) && return false

    # check parent is func def
    return is_in_funcdef(x)
end

function add_binding(x, state, scope=state.scope)
    if bindingof(x) isa Binding
        b = bindingof(x)
        b.prev = nothing
        b.next = nothing
        if isidentifier(b.name)
            name = valofid(b.name)
        elseif CSTParser.ismacroname(b.name) # must be getfield
            # name = CSTParser.rhs_getfield(b.name)
            name = string(Expr(b.name))
        elseif isoperator(b.name)
            name = string(Expr(b.name))
        else
            return
        end
        # check for global marker
        if isglobal(name, scope)
            scope = _get_global_scope(state.scope)
        end

        if CSTParser.defines_macro(x)
            scope.names[string("@", name)] = b
            mn = CSTParser.get_name(x)
            if isidentifier(mn)
                setref!(mn, b)
            end
        else
            if name_is_getfield(b.name)# && b.type == CoreTypes.Function
                # Question: should `b.name` include the getfield itself?
                # Binding name is part of a getfield : `A.name` so is either
                # 1. Overloading of a function
                # 2. Setting of a field or property
                # We only care about 1.
                resolve_ref(parentof(parentof(b.name)).args[1], scope, state)
                lhs_ref = refof_maybe_getfield(parentof(parentof(b.name)).args[1])
                if lhs_ref === nothing
                    # We don't know what we're assigning to, do nothing
                else
                    if lhs_ref isa SymbolServer.ModuleStore && haskey(lhs_ref.vals, Symbol(name))
                        # Overloading
                        tls = retrieve_toplevel_scope(b.val)
                        tls === nothing && return # Shouldn't happen
                        if haskey(tls.names, name) && eventually_overloads(tls.names[name], lhs_ref.vals[Symbol(name)], state.server)
                            # Though we're explicitly naming a function for overloading, it has already been imported to the toplevel scope.
                            overload_method(tls, b, VarRef(lhs_ref.name, Symbol(name)))
                            b.prev = tls.names[name]
                            b.prev.next = b
                            tls.names[name] = b
                        elseif isexportedby(name, lhs_ref)
                            tls.names[name] = b
                            b.prev = maybe_lookup(lhs_ref[Symbol(name)], state.server)
                        else
                            overload_method(tls, b, VarRef(lhs_ref.name, Symbol(name)))
                        end
                    elseif lhs_ref isa Binding && lhs_ref.type == CoreTypes.Module
                        if hasscope(lhs_ref.val) && haskey(scopeof(lhs_ref.val).names, name)
                            b.prev = scopeof(lhs_ref.val).names[name]
                            scopeof(lhs_ref.val).names[name] = b
                        end
                    end
                end

            elseif scopehasbinding(scope, name)
                b.prev = scope.names[name]
                scope.names[name] = b
                b.prev.next = b
            else
                scope.names[name] = b
            end
            # hoist binding for inner constructor to parent scope
            if CSTParser.defines_struct(scope.expr) && CSTParser.defines_function(x) && parentof(scope) isa Scope
                return add_binding(x, state, parentof(scope))
            end
        end
        infer_type(b, scope, state)
    elseif bindingof(x) isa SymbolServer.SymStore
        scope.names[valofid(x)] = bindingof(x)
    end
end

name_is_getfield(x) = parentof(x) isa EXPR && parentof(parentof(x)) isa EXPR && CSTParser.is_getfield_w_quotenode(parentof(parentof(x)))


"""
eventually_overloads(b, x, server)


"""
eventually_overloads(b::Binding, ss::SymbolServer.SymStore, server) = (b.val == ss || b.prev == ss) || (b.prev !== nothing && eventually_overloads(b.prev, ss, server))

eventually_overloads(b::Binding, ss::SymbolServer.VarRef, server) = eventually_overloads(b, maybe_lookup(ss, server), server)

eventually_overloads(b, ss, server) = false



function hoist_prev_binding(b, name, scope, state)
    scope === nothing && return
    if scope.modules !== nothing
        if scopehasmodule(scope, Symbol(valofid(parentof(parentof(b.name)).args[1]))) # this scope (s1) has a module with matching name
            mod = getscopemodule(scope, Symbol(valofid(parentof(parentof(b.name)).args[1])))
            if mod isa SymbolServer.ModuleStore && haskey(mod, Symbol(name))
                b.prev = maybe_lookup(mod[Symbol(name)], state.server)
            end
        end
        return # We've reached a scope that loads modules, no need to keep searching upwards
    end
    return hoist_prev_binding(b, name, parentof(scope), state)
end

isglobal(name, scope) = false
isglobal(name::String, scope) = scope !== nothing && scopehasbinding(scope, "#globals") && name in scope.names["#globals"].refs

function mark_globals(x::EXPR, state)
    if headof(x) === :global
        if !scopehasbinding(state.scope, "#globals")
            state.scope.names["#globals"] = Binding(EXPR(:IDENTIFIER, EXPR[], nothing, 0, 0, "#globals", nothing, nothing), nothing, nothing, [], nothing, nothing)
        end
        for i = 2:length(x.args)
            if isidentifier(x.args[i]) && !scopehasbinding(state.scope, valofid(x.args[i]))
                push!(state.scope.names["#globals"].refs, valofid(x.args[i]))
            end
        end
    end
end

function name_extends_imported_method(b::Binding)
    if b.type == CoreTypes.Function && CSTParser.hasparent(b.name) && CSTParser.is_getfield(parentof(b.name))
        if refof_maybe_getfield(parentof(b.name)[1]) !== nothing

        end
    end
end
