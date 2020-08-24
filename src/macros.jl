function handle_macro(@nospecialize(x), state) end
function handle_macro(x::EXPR, state)
    !is_macro_call(x) && return
    if is_macroname(x[1])
        state(x[1])
        if _points_to_Base_macro(x[1], :deprecate, state) && length(x) == 3
            if bindingof(x[2]) !== nothing
                return
            elseif CSTParser.is_func_call(x[2])
                # add deprecated method
                # add deprecated function binding and args in new scope
                mark_binding!(x[2], x)
                mark_sig_args!(x[2])
                s0 = state.scope # store previous scope
                state.scope = Scope(s0, x, Dict(), nothing, nothing)
                setscope!(x, state.scope) # tag new scope to generating expression
                state(x[2])
                state(x[3])
                state.scope = s0
            elseif isidentifier(x[2])
                mark_binding!(x[2], x)
            end
        elseif _points_to_Base_macro(x[1], :deprecate_binding, state) && length(x) == 3 && isidentifier(x[2]) && isidentifier(x[3])
            setref!(x[2], refof(x[3]))
        elseif _points_to_Base_macro(x[1], :eval, state) && length(x) == 2 && state isa Toplevel
            # Create scope around eval'ed expression. This ensures anybindings are
            # correctly hoisted to the top-level scope.
            setscope!(x, Scope(x))
            setparent!(scopeof(x), state.scope)
            s0 = state.scope
            state.scope = scopeof(x)
            interpret_eval(x[2], state)
            state.scope = s0
        elseif _points_to_Base_macro(x[1], :irrational, state) && length(x) == 4
            mark_binding!(x[2], x)
        elseif _points_to_Base_macro(x[1], :enum, state)
            for i = 2:length(x)
                if !ispunctuation(x[i])
                    if bindingof(x[i]) !== nothing
                        break
                    end
                    if i == 3 && typof(x[i]) === CSTParser.Begin
                        for j in 1:length(x[i][2])
                            mark_binding!(x[i][2][j], x)
                        end
                        break
                    end
                    mark_binding!(x[i], x)
                end
            end
        elseif _points_to_Base_macro(x[1], :goto, state)
            if length(x) == 2 && isidentifier(x[2])
                setref!(x[2], Binding(noname, nothing, nothing, EXPR[], nothing, nothing))
            end
        elseif _points_to_Base_macro(x[1], :label, state)
            if length(x) == 2 && isidentifier(x[2])
                mark_binding!(x[2])
            end
        elseif length(x[1]) == 2 && isidentifier(x[1][2]) && valofid(x[1][2]) == "nospecialize"
            for i = 2:length(x)
                if !ispunctuation(x[i])
                    if bindingof(x[i]) !== nothing
                        break
                    end
                    mark_binding!(x[i], x)
                end
            end
        elseif _points_to_arbitrary_macro(x[1], :Turing, :model, state) && length(x) == 2 &&
            is_binary_call(x[2], CSTParser.Tokens.EQ) &&
            typof(x[2][3]) === CSTParser.Begin && length(x[2][3]) == 3 && typof(x[2][3][2]) === CSTParser.Block
            for i = 1:length(x[2][3][2])
                ex = x[2][3][2][i]
                if is_binary_call(ex, CSTParser.Tokens.APPROX)
                    mark_binding!(ex)
                end
            end
        elseif _points_to_arbitrary_macro(x[1], :JuMP, :variable, state)
            if length(x) < 3
                return
            elseif length(x) >= 5 && ispunctuation(x[2])
                _mark_JuMP_binding(x[5])
            else
                _mark_JuMP_binding(x[3])
            end
        elseif (_points_to_arbitrary_macro(x[1], :JuMP, :expression, state) ||
            _points_to_arbitrary_macro(x[1], :JuMP, :NLexpression, state) ||
            _points_to_arbitrary_macro(x[1], :JuMP, :constraint, state) || _points_to_arbitrary_macro(x[1], :JuMP, :NLconstraint, state)) && length(x) > 1
            if ispunctuation(x[2])
                if length(x) == 8
                    _mark_JuMP_binding(x[5])
                end
            else
                if length(x) == 4
                    _mark_JuMP_binding(x[3])
                end
            end
        end
    elseif typof(x[1]) == CSTParser.GlobalRefDoc && length(x) == 3 && CSTParser.isliteral(x[2]) && kindof(x[2]) === CSTParser.Tokens.TRIPLE_STRING && isidentifier(x[3])
        mark_binding!(x[3])
        setref!(x[3], bindingof(x[3]))
    end
end

function _rem_ref(x::EXPR)
    if typof(x) === CSTParser.Ref && length(x) > 0
        return x[1]
    end
    return x
end

function _mark_JuMP_binding(arg)
    if isidentifier(arg) || typof(arg) === CSTParser.Ref
        mark_binding!(_rem_ref(arg))
    elseif is_binary_call(arg, CSTParser.Tokens.EQEQ) || is_binary_call(arg, CSTParser.Tokens.LESS_EQ)  || is_binary_call(arg, CSTParser.Tokens.GREATER_EQ)
        if isidentifier(arg[1]) || typof(arg[1]) === CSTParser.Ref
            mark_binding!(_rem_ref(arg[1]))
        else
            mark_binding!(_rem_ref(arg[3]))
        end
    elseif typof(arg) === CSTParser.Comparison && length(arg) == 5
        mark_binding!(_rem_ref(arg[3]))
    end
end

function _points_to_Base_macro(x::EXPR, name, state)
    is_getfield_w_quotenode(x) && return _points_to_Base_macro(x[3][1], name, state)
    targetmacro =  maybe_lookup(getsymbolserver(state.server)[:Base][Symbol("@", name)], state.server)
    length(x) == 2 && isidentifier(x[2]) && Symbol(valofid(x[2])) == name && (ref = refof(x[2])) !== nothing &&
    (ref == targetmacro || (ref isa Binding && ref.val == targetmacro))
end

function _points_to_arbitrary_macro(x::EXPR, module_name, name, state)
    length(x) == 2 && isidentifier(x[2]) && valof(x[2]) == name && haskey(getsymbolserver(state.server), Symbol(module_name)) && haskey(getsymbolserver(state.server)[Symbol(module_name)], Symbol("@", name)) && (refof(x[2]) == maybe_lookup(getsymbolserver(state.server)[Symbol(module_name)][Symbol("@", name)], state.server) ||
    (refof(x[2]) isa Binding && refof(x[2]).val == maybe_lookup(getsymbolserver(state.server)[Symbol(module_name)][Symbol("@", name)], state.server)))
end

maybe_lookup(x, server) = x isa SymbolServer.VarRef ? SymbolServer._lookup(x, getsymbolserver(server), true) : x

function maybe_eventually_get_id(x::EXPR)
    if isidentifier(x)
        return x
    elseif is_invis_brackets(x)
        return maybe_eventually_get_id(x[2])
    end
    return nothing
end

is_eventually_interpolated(x::EXPR) = is_invis_brackets(x) ? is_eventually_interpolated(x[2]) : is_unary_call(x) && CSTParser.is_exor(x[1])
isquoted(x::EXPR) = typof(x) === CSTParser.Quotenode && length(x) == 2 && kindof(x[1]) === CSTParser.Tokens.COLON
maybeget_quotedsymbol(x::EXPR) = isquoted(x) ? maybe_eventually_get_id(x[2]) : nothing

function is_loop_iterator(x::EXPR)
    CSTParser.is_range(x) &&
    ((parentof(x) isa EXPR && typof(parentof(x)) === CSTParser.For) ||
    (parentof(x) isa EXPR && parentof(parentof(x)) isa EXPR && typof(parentof(parentof(x))) === CSTParser.For))
end

"""
    maybe_quoted_list(x::EXPR)

Try and get a list of quoted symbols from x. Return nothing if not possible.
"""
function maybe_quoted_list(x::EXPR)
    names = EXPR[]
    if typof(x) === CSTParser.Vect || typof(x) === CSTParser.TupleH
        for i = 1:length(x)
            CSTParser.ispunctuation(x[i]) && continue
            name = maybeget_quotedsymbol(x[i])
            if name !== nothing
                push!(names, name)
            else
                return nothing
            end
        end
        return names
    end
end

"""
interpret_eval(x::EXPR, state)

Naive attempt to interpret `x` as though it has been eval'ed. Lifts
any bindings made within the scope of `x` to the toplevel and replaces 
(some) interpolated binding names with the value where possible.
"""
function interpret_eval(x::EXPR, state)
    # make sure we have bindings etc
    state(x)
    tls = retrieve_toplevel_scope(x)
    for ex in collect_expr_with_bindings(x)
        b = bindingof(ex)
        if isidentifier(b.name)
            # The name of the binding is fixed
            add_binding(ex, state, tls)
        elseif CSTParser.is_exor(b.name)
            # The name of the binding is variable, we need to work out what the
            # interpolated symbol points to.
            variable_name = parentof(b.name)[2]
            resolve_ref(variable_name, state.scope, state)
            if (ref = refof(variable_name)) isa Binding
                if is_assignment(ref.val) && (rhs = maybeget_quotedsymbol(ref.val[3])) !== nothing
                    # `name = :something`
                    toplevel_binding = Binding(rhs, b.val, b.type, [], nothing, nothing)
                    if scopehasbinding(tls, valofid(toplevel_binding.name))
                        toplevel_binding.prev = tls.names[valofid(toplevel_binding.name)]
                        tls.names[valofid(toplevel_binding.name)] = toplevel_binding
                        toplevel_binding.prev.next = toplevel_binding
                    else
                        tls.names[valofid(toplevel_binding.name)] = toplevel_binding
                    end
                elseif is_loop_iterator(ref.val) && (names = maybe_quoted_list(ref.val[3])) !== nothing
                    # name is of a collection of quoted symbols
                    for name in names
                        toplevel_binding = Binding(name, b.val, b.type, [], nothing, nothing)
                        if scopehasbinding(tls, valofid(toplevel_binding.name))
                            toplevel_binding.prev = tls.names[valofid(toplevel_binding.name)]
                            tls.names[valofid(toplevel_binding.name)] = toplevel_binding
                            toplevel_binding.prev.next = toplevel_binding
                        else
                            tls.names[valofid(toplevel_binding.name)] = toplevel_binding
                        end
                    end
                end
            end
        end
    end
end

function collect_expr_with_bindings(x, bound_exprs=EXPR[])
    if hasbinding(x)
        push!(bound_exprs, x)
        # Assuming here that if an expression has a binding we don't want anything bound to chlid nodes.
    elseif !((CSTParser.defines_function(x) && !(is_eventually_interpolated(x[1]))) || CSTParser.defines_macro(x) || typof(x) === CSTParser.Export)
        for a in x
            collect_expr_with_bindings(a, bound_exprs)
        end
    end
    return bound_exprs
end
