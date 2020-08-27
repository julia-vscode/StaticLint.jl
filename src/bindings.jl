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
    printstyled(io, "Binding(", Expr(b.name),
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
    if is_binary_call(x)
        if kindof(x[2]) === CSTParser.Tokens.EQ
            if CSTParser.is_func_call(x[1])
                name = CSTParser.get_name(x)
                mark_binding!(x)
                mark_sig_args!(x[1])
                if isidentifier(name)
                    setref!(name, bindingof(x))
                end
            elseif is_curly(x[1])
                mark_typealias_bindings!(x)
            elseif !is_getfield(x[1])
                mark_binding!(x[1], x)
            end
        elseif kindof(x[2]) === CSTParser.Tokens.ANON_FUNC
            mark_binding!(x[1], x)
        end
    elseif is_where(x)
        for i = 3:length(x)
            ispunctuation(x[i]) && continue
            mark_binding!(x[i])
        end
    elseif typof(x) === CSTParser.For
        markiterbinding!(x[2])
    elseif typof(x) === CSTParser.Generator
        for i = 3:length(x)
            ispunctuation(x[i]) && continue
            markiterbinding!(x[i])
        end
    elseif typof(x) === CSTParser.Filter
        for i = 1:length(x) - 2
            ispunctuation(x[i]) && continue
            markiterbinding!(x[i])
        end
    elseif typof(x) === CSTParser.Flatten && length(x) === 1 && length(x[1]) >= 3 && length(x[1][1]) >= 3
        for i = 3:length(x[1][1])
            ispunctuation(x[1][1][i]) && continue
            markiterbinding!(x[1][1][i])
        end
        for i = 3:length(x[1])
            ispunctuation(x[1][i]) && continue
            markiterbinding!(x[1][i])
        end
    elseif typof(x) === CSTParser.Do
        if is_tuple(x[3])
            for i in 1:length(x[3])
                ispunctuation(x[3][i]) && continue
                mark_binding!(x[3][i])
            end
        end
    elseif typof(x) === FunctionDef || CSTParser.defines_macro(x)
        name = CSTParser.get_name(x)
        x.meta.binding = Binding(name, x, CoreTypes.Function, [], nothing, nothing)
        if isidentifier(name)
            setref!(name, bindingof(x))
        end
        mark_sig_args!(CSTParser.get_sig(x))
    elseif CSTParser.defines_module(x)
        x.meta.binding = Binding(x[2], x, CoreTypes.Module, [], nothing, nothing)
        setref!(x[2], bindingof(x))
    elseif typof(x) === CSTParser.Try && length(x) > 3 && isidentifier(x[4])
        mark_binding!(x[4])
        setref!(x[4], bindingof(x[4]))
    elseif CSTParser.defines_datatype(x)
        name = CSTParser.get_name(x)
        x.meta.binding = Binding(name, x, CoreTypes.DataType, [], nothing, nothing)
        if isidentifier(name)
            setref!(name, bindingof(x))
        end
        mark_parameters(CSTParser.get_sig(x))
        if CSTParser.defines_struct(x) # mark field block
            blocki = typof(x[3]) === CSTParser.Block ? 3 : 4
            for i in 1:length(x[blocki])
                CSTParser.defines_function(x[blocki][i]) && continue
                mark_binding!(x[blocki][i])
            end
        end
    elseif typof(x) === CSTParser.Local
        if length(x) == 2
            if isidentifier(x[2])
                mark_binding!(x[2])
                setref!(x[2], bindingof(x[2]))
            elseif is_tuple(x[2])
                for i = 1:length(x[2])
                    if isidentifier(x[2][i])
                        mark_binding!(x[2][i])
                        setref!(x[2][i], bindingof(x[2][i]))
                    end
                end
            end
        end

    end
end


function mark_binding!(x::EXPR, val=x)
    if is_kwarg(x) || (is_declaration(x) && is_tuple(x[1]))
        mark_binding!(x[1], x)
    elseif is_tuple(x) || is_parameters(x)
        for arg in x
            ispunctuation(arg) && continue
            mark_binding!(arg, val)
        end
    elseif typof(x) === CSTParser.InvisBrackets
        mark_binding!(CSTParser.rem_invis(x), val)
    elseif !(is_unary_call(x) && kindof(x[1]) === CSTParser.Tokens.DECLARATION)
        if !hasmeta(x)
            x.meta = Meta()
        end
        x.meta.binding = Binding(CSTParser.get_name(x), val, nothing, [], nothing, nothing)
    end
    return x
end


function mark_parameters(sig::EXPR)
    signame = CSTParser.rem_where_subtype(sig)
    if is_curly(signame)
        for i = 3:length(signame) - 1
            ispunctuation(signame[i]) && continue
            mark_binding!(signame[i])
        end
    end
    return sig
end


function markiterbinding!(iter::EXPR)
    if is_binary_call(iter) && kindof(iter[2]) in (CSTParser.Tokens.EQ, CSTParser.Tokens.IN, CSTParser.Tokens.ELEMENT_OF)
        mark_binding!(iter[1], iter)
    elseif typof(iter) === CSTParser.Block
        for i = 1:length(iter)
            ispunctuation(iter[i]) && continue
            markiterbinding!(iter[i])
        end
    end
    return iter
end

function mark_sig_args!(x::EXPR)
    if is_call(x) || is_tuple(x)
        if typof(x[1]) === CSTParser.InvisBrackets && is_declaration(x[1][2])
            mark_binding!(x[1][2])
        end
        for i = 2:length(x) - 1
            a = x[i]
            if is_parameters(a)
                for j = 1:length(a)
                    aa = a[j]
                    if !ispunctuation(aa)
                        mark_binding!(aa)
                    end
                end
            elseif !ispunctuation(a)
                mark_binding!(a)
            end
        end
    elseif is_where(x)
        for i in 3:length(x)
            if !ispunctuation(x[i])
                mark_binding!(x[i])
            end
        end
        mark_sig_args!(x[1])
    elseif is_invis_brackets(x)
        mark_sig_args!(CSTParser.rem_invis(x))
    elseif is_binary_call(x)
        if kindof(x[2]) == CSTParser.Tokens.DECLARATION
            mark_sig_args!(x[1])
        else
            mark_binding!(x[1])
            mark_binding!(x[3])
        end
    elseif is_unary_call(x) && typof(x[2]) == CSTParser.InvisBrackets
        mark_binding!(x[2][2])
    end
end

function mark_typealias_bindings!(x::EXPR)
    mark_binding!(x, x)
    setscope!(x, Scope(x))
    for i = 2:length(x[1])
        if isidentifier(x[1][i])
            mark_binding!(x[1][i])
        elseif is_binary_call(x[1][i]) && kindof(x[1][i][2]) === CSTParser.Tokens.ISSUBTYPE && isidentifier(x[1][i][1])
            mark_binding!(x[1][i][1])
        end
    end
    return x
end

rem_wheres_decls(x) = (is_where(x) || is_declaration(x)) ? x[1] : x

function is_in_funcdef(x)
    if !(parentof(x) isa EXPR)
        return false
    elseif is_where(parentof(x)) || typof(parentof(x)) === CSTParser.InvisBrackets
        return is_in_funcdef(parentof(x))
    elseif typof(parentof(x)) === FunctionDef || CSTParser.is_assignment(parentof(x))
        return true
    else
        return false
    end
end

function _in_func_def(x::EXPR)
    # only called in WhereOpCall
    # check 1st arg contains a call (or op call)
    ex = rem_wheres_decls(x[1])

    !(is_call(ex) || (is_binary_call(ex) && kindof(ex[2]) !== CSTParser.Tokens.DOT) || is_unary_call(ex)) && return false

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
        elseif is_macroname(b.name)
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
                resolve_ref(parentof(parentof(b.name))[1], scope, state)
                lhs_ref = refof_maybe_getfield(parentof(parentof(b.name))[1])
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

name_is_getfield(x) = parentof(x) isa EXPR && parentof(parentof(x)) isa EXPR && is_getfield_w_quotenode(parentof(parentof(x)))


"""
eventually_overloads(b, x, server)


"""
eventually_overloads(b::Binding, ss::SymbolServer.SymStore, server) = (b.val == ss || b.prev == ss) || (b.prev !== nothing && eventually_overloads(b.prev, ss, server))

eventually_overloads(b::Binding, ss::SymbolServer.VarRef, server) = eventually_overloads(b, maybe_lookup(ss, server), server)

eventually_overloads(b, ss, server) = false



function hoist_prev_binding(b, name, scope, state)
    scope === nothing && return
    if scope.modules !== nothing
        if scopehasmodule(scope, Symbol(valofid(parentof(parentof(b.name))[1]))) # this scope (s1) has a module with matching name
            mod = getscopemodule(scope, Symbol(valofid(parentof(parentof(b.name))[1])))
            if mod isa SymbolServer.ModuleStore && haskey(mod, Symbol(name))
                b.prev = maybe_lookup(mod[Symbol(name)], state.server)
            end
        end
        return # We've reached a scope that loads modules, no need to keep searching upwards
    end
    return hoist_prev_binding(b, name, parentof(scope), state)
end

isglobal(name, scope) = false
isglobal(name::String, scope) = scopehasbinding(scope, "#globals") && name in scope.names["#globals"].refs

function mark_globals(x::EXPR, state)
    if typof(x) === CSTParser.Global
        if !scopehasbinding(state.scope, "#globals")
            state.scope.names["#globals"] = Binding(EXPR(CSTParser.IDENTIFIER, EXPR[], 0, 0, "#globals", CSTParser.NoKind, false, nothing, nothing), nothing, nothing, [], nothing, nothing)
        end
        for i = 2:length(x)
            if isidentifier(x[i]) && !scopehasbinding(state.scope, valofid(x[i]))
                push!(state.scope.names["#globals"].refs, valofid(x[i]))
            end
        end

    end
end

function name_extends_imported_method(b::Binding)
    if b.type == CoreTypes.Function && hasparent(b.name) && is_getfield(parentof(b.name))
        if refof_maybe_getfield(parentof(b.name)[1]) !== nothing

        end
    end
end
