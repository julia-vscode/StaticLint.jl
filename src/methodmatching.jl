function arg_type(arg, ismethod)
    # Strip `@nospecialize` and `x...` wrappers — the binding/type info
    # lives on the inner expression in both cases.
    arg = unwrap_nospecialize(arg)
    if CSTParser.issplat(arg) && length(arg.args) >= 1
        arg = arg.args[1]
    end
    if ismethod
        if hasbinding(arg)
            if bindingof(arg) isa Binding && bindingof(arg).type !== nothing
                type = bindingof(arg).type
                if type isa Binding && type.val isa SymbolServer.DataTypeStore
                    type = type.val
                elseif type isa Binding && CoreTypes.isdatatype(type.type)
                    # Bound through a typevar (the link's `.type` is the
                    # `DataType` meta-type). We don't know the concrete
                    # constraint statically — fall back to `Any` so the
                    # type-intersection check stays permissive.
                    return CoreTypes.Any
                end
                return type
            end
        end
    else
        if hasref(arg)
            if refof(arg) isa Binding && refof(arg).type !== nothing
                type = refof(arg).type
                if type isa Binding && type.val isa SymbolServer.DataTypeStore
                    type = type.val
                end
                return type
            end
        elseif headof(arg) === :STRING
            return CoreTypes.String
        elseif headof(arg) === :CHAR
            return CoreTypes.Char
        elseif headof(arg) === :FLOAT
            return CoreTypes.Float64
        elseif headof(arg) === :INTEGER
            return CoreTypes.Int
        elseif headof(arg) === :HEXINT
            if length(arg.val) < 5
                return CoreTypes.UInt8
            elseif length(arg.val) < 7
                return CoreTypes.UInt16
            elseif length(arg.val) < 11
                return CoreTypes.UInt32
            else
                return CoreTypes.UInt64
            end
        elseif headof(arg) === :TRUE || headof(arg) === :FALSE
            return CoreTypes.Bool
        elseif isquotedsymbol(arg)
            return SymbolServer.stdlibs[:Core][:Symbol]
        end
    end
    # VarRef(VarRef(nothing, :Core), :Any)
    CoreTypes.Any
end

isquotedsymbol(x) = x isa EXPR && x.head === :quotenode && length(x.args) == 1 && x.args[1].head === :IDENTIFIER && hastrivia(x)

# Extract the name from a kwarg in a `:parameters` block. The entry may
# be a bare identifier (sig form `f(a; p)`), a kwarg with default
# (`p = v`), or a typed decl (`p::T`). Bare identifiers have no `.args`,
# so we can't always reach `.args[1]`.
function _kw_name(x::EXPR)
    x.args !== nothing && !isempty(x.args) ? x.args[1] : x
end

function call_arg_types(call::EXPR, ismethod)
    types, kws = [], []
    call.args === nothing && return types, kws
    if length(call.args) > 1 && headof(call.args[2]) === :parameters
        for i = 1:length(call.args[2].args)
            push!(kws, _kw_name(call.args[2].args[i]))
        end
        for i = 3:length(call.args)
            if CSTParser.iskwarg(call.args[i])
                push!(kws, call.args[i].args[1])
            else
                push!(types, arg_type(call.args[i], ismethod))
            end
        end
    else
        for i = 2:length(call.args)
            if CSTParser.iskwarg(call.args[i])
                # `f(a, b, kw = v)` — kwarg without semicolon. Pull it
                # into `kws` so arity matches `method_arg_types`'s view.
                push!(kws, call.args[i].args[1])
            else
                push!(types, arg_type(call.args[i], ismethod))
            end
        end
    end
    types, kws
end

function method_arg_types(call::EXPR)
    types, opts, kws = [], [], []
    call.args === nothing && return types, opts, kws
    if length(call.args) > 1 && headof(call.args[2]) === :parameters
        for i = 1:length(call.args[2].args)
            push!(kws, _kw_name(call.args[2].args[i]))
        end
        for i = 3:length(call.args)
            if CSTParser.iskwarg(call.args[i])
                push!(opts, arg_type(call.args[i].args[1], true))
            else
                push!(types, arg_type(call.args[i], true))
            end
        end
    else
        for i = 2:length(call.args)
            if CSTParser.iskwarg(call.args[i])
                push!(opts, arg_type(call.args[i].args[1], true))
            else
                push!(types, arg_type(call.args[i], true))
            end
        end
    end
    types, opts, kws
end

function find_methods(x::EXPR, store)
    possibles = []
    if iscall(x)
        length(x.args) === 0 && return possibles
        func_ref = refof_call_func(x)
        func_ref === nothing && return possibles
        args, kws = call_arg_types(x, false)
        if func_ref isa Binding && func_ref.val isa SymbolServer.FunctionStore ||
            func_ref isa Binding && func_ref.val isa SymbolServer.DataTypeStore
            func_ref = func_ref.val
        end
        if func_ref isa SymbolServer.FunctionStore || func_ref isa SymbolServer.DataTypeStore
            for method in func_ref.methods
                if match_method(args, kws, method, store)
                    push!(possibles, method)
                end
            end
        elseif func_ref isa Binding
            if (CoreTypes.isfunction(func_ref.type) || CoreTypes.isdatatype(func_ref.type)) && func_ref.val isa EXPR
                for method in func_ref.refs
                    method = get_method(method)
                    if method !== nothing
                        if method isa SymbolServer.FunctionStore
                            for method1 in method.methods
                                if match_method(args, kws, method1, store)
                                    push!(possibles, method1)
                                end
                            end
                        elseif match_method(args, kws, method, store)
                            push!(possibles, method)
                        end
                    end
                end
            elseif (method = method_of_callable_datatype(func_ref)) !== nothing
                if match_method(args, kws, method, store)
                    push!(possibles, method)
                end
            end
        end
    end
    possibles
end

"""
    is_explicit_vararg_decl(arg)

True if `arg` is a method-arg declaration of the form `x::Vararg` or
`x::Vararg{...}`. Unlike `CSTParser.issplat`, this matches the explicit
`::Vararg` spelling rather than the `x...` splat.
"""
function is_explicit_vararg_decl(arg)
    isdeclaration(arg) || return false
    length(arg.args) >= 2 || return false
    t = arg.args[2]
    isidentifier(t) && valofid(t) == "Vararg" && return true
    iscurly(t) && length(t.args) >= 1 && isidentifier(t.args[1]) && valofid(t.args[1]) == "Vararg" && return true
    return false
end

"""
    bounded_vararg_N(arg)

Return the literal `N` if `arg` is a method-arg declaration of the form
`x::Vararg{T,N}` with an integer literal `N`; otherwise `nothing`.
Distinguishes bounded `Vararg{T,N}` (consumes exactly N args) from the
unbounded `Vararg{T}` and parametric `Vararg{T,N} where N`.
"""
function bounded_vararg_N(arg)
    isdeclaration(arg) || return nothing
    length(arg.args) >= 2 || return nothing
    t = arg.args[2]
    iscurly(t) || return nothing
    length(t.args) == 3 || return nothing
    isidentifier(t.args[1]) && valofid(t.args[1]) == "Vararg" || return nothing
    N_expr = t.args[3]
    CSTParser.headof(N_expr) === :INTEGER || return nothing
    N_expr.val isa AbstractString || return nothing
    return tryparse(Int, N_expr.val)
end

function match_method(args::Vector{Any}, kws::Vector{Any}, method::SymbolServer.MethodStore, store)
    !isempty(kws) && isempty(method.kws) && return false
    nsig = length(method.sig)
    if nsig > 0 && last(method.sig)[2] isa SymbolServer.FakeTypeofVararg
        va = last(method.sig)[2]
        n_no_vararg = nsig - 1
        # Bounded `Vararg{T,N}` consumes exactly N args at that position;
        # unbounded `Vararg{T}` and `Vararg{T,N} where N` accept any count.
        if isdefined(va, :N) && va.N isa Integer
            length(args) == n_no_vararg + va.N || return false
        else
            length(args) >= n_no_vararg || return false
        end
        for i in 1:n_no_vararg
            t = method.sig[i][2]
            _has_type_intersection(args[i], t, store) || return false
        end
        for i in (n_no_vararg + 1):length(args)
            _has_type_intersection(args[i], va.T, store) || return false
        end
        return true
    end
    length(args) == nsig || return false
    for i in 1:length(args)
        t = method.sig[i][2]
        _has_type_intersection(args[i], t, store) || return false
    end
    return true
end

# Resolve a type-position EXPR (`String`, `Vector{Int}`, …) to the
# SymbolServer type used by `_has_type_intersection`. A type name often
# `refof`s to its constructor `FunctionStore`; we follow `extends` back
# to the `DataTypeStore`. Falls back to `CoreTypes.Any` so callers stay
# permissive if resolution fails.
function _resolve_type_expr(t, store)
    if iscurly(t) && length(t.args) >= 1
        t = t.args[1]
    end
    hasref(t) || return CoreTypes.Any
    r = refof(t)
    if r isa SymbolServer.DataTypeStore
        return r
    elseif r isa SymbolServer.FunctionStore
        dt = SymbolServer._lookup(r.extends, store)
        return dt === nothing ? CoreTypes.Any : dt
    elseif r isa Binding && r.type isa Binding && r.type.val isa SymbolServer.DataTypeStore
        # The reference points at a concrete locally-defined DataType via
        # an intermediate Binding. A bare `r.type isa DataTypeStore` would
        # also catch typevars (whose binding.type === `Core.DataType` —
        # the meta-type, not a usable constraint), so we don't.
        return r.type.val
    end
    return CoreTypes.Any
end

function match_method(args::Vector{Any}, kws::Vector{Any}, method::EXPR, store)
    margs, mopts, mkws = [], [], []
    vararg = false
    vararg_N = nothing
    if CSTParser.defines_struct(method)
        for i in 1:length(method.args[3].args)
            arg = method.args[3].args[i]
            if defines_function(arg)
                # Hit an inner constructor so forget about the default one.
                for arg in method.args[3].args
                    if defines_function(arg)
                        !match_method(args, kws, arg, store) && return false
                    end
                end
                return true
            end
            push!(margs, arg_type(arg, true))
        end
    else
        # `rem_wheres_decls` strips outer `where` clauses (so parametric
        # `Vararg{T,N} where N` is reachable) and the outer return-type
        # decl `f(...)::T` (so the call expression sits at the top).
        # `arg_type` itself unwraps `<decl>...` splats and `@nospecialize`
        # wrappers internally, so we don't need to walk inner decls here.
        sig = CSTParser.rem_wheres_decls(CSTParser.get_sig(method))

        # Bare forward declaration `function f end`: `get_sig` returns the
        # lone name (an EXPR with `args === nothing`), no signature to match.
        # It is not a method, so it matches no call.
        sig.args === nothing && return false

        # Element type for an explicit `::Vararg{T,...}` slot. `arg_type`
        # on the decl returns the *Vararg* binding, not `T`, so we extract
        # `T` from the AST and use it for the trailing-arg type check.
        vararg_T = nothing
        if length(sig.args) > 0
            last_arg = unwrap_nospecialize(last(sig.args))
            vararg_N = bounded_vararg_N(last_arg)
            if vararg_N !== nothing || is_explicit_vararg_decl(last_arg)
                vararg = true
                ty = last_arg.args[2]
                if iscurly(ty) && length(ty.args) >= 2
                    vararg_T = _resolve_type_expr(ty.args[2], store)
                end
            end
            if CSTParser.issplat(last_arg)
                vararg = true
            end
        end

        margs, mopts, mkws = method_arg_types(sig)
    end
    !isempty(kws) && isempty(mkws) && return false

    # Bounded `Vararg{T,N}`: require exactly nfixed + N positional args
    # and match the trailing slots against `T`.
    if vararg_N !== nothing
        nfixed = length(margs) - 1
        length(args) == nfixed + vararg_N || return false
        tail = vararg_T === nothing ? CoreTypes.Any : vararg_T
        for i in 1:nfixed
            _has_type_intersection(args[i], margs[i], store) || return false
        end
        for i in (nfixed + 1):length(args)
            _has_type_intersection(args[i], tail, store) || return false
        end
        return true
    end

    if length(margs) < length(args)
        for i in 1:min(length(mopts), length(args) - length(margs))
            push!(margs, mopts[i])
        end
        if vararg
            pad = vararg_T === nothing ? CoreTypes.Any : vararg_T
            for _ in 1:length(args) - length(margs)
                push!(margs, pad)
            end
        end
    end

    if length(args) == length(margs) || (vararg && length(args) == length(margs) - 1)
        for i in 1:length(args)
            _has_type_intersection(args[i], margs[i], store) || return false
        end
        return true
    end
    return false
end

function refof_call_func(x)
    if isidentifier(first(x.args)) && hasref(first(x.args))
        return refof(first(x.args))
    elseif is_getfield_w_quotenode(x.args[1]) && (rhs = rhs_of_getfield(x.args[1])) !== nothing && hasref(rhs)
        return refof(rhs)
    else
        return
    end
end

function is_sig_of_method(sig::EXPR, method = maybe_get_parent_fexpr(sig, defines_function))
    method !== nothing && sig == CSTParser.get_sig(method)
end

function method_of_callable_datatype(b::Binding)
    if b.type isa Binding && b.type.type === CoreTypes.DataType
        for ref in b.type.refs
            if ref isa EXPR && ref.parent isa EXPR && isdeclaration(ref.parent) && is_in_fexpr(ref.parent, x -> x.parent isa EXPR && x.parent.head === :call && x == x.parent.args[1] && is_in_funcdef(x.parent))
                return get_parent_fexpr(ref, defines_function)
            end
        end
    end
end
