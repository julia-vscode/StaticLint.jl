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
                state.scope = Scope(s0, x, Dict(), nothing, false)
                setscope!(x, state.scope) # tag new scope to generating expression
                state(x[2])
                state(x[3])
                state.scope = s0
            elseif isidentifier(x[2])
                mark_binding!(x[2], x)
            end
        elseif _points_to_Base_macro(x[1], :eval, state) && length(x) == 2 && state isa Toplevel # Only do this in top-level pass?
            setscope!(x[2], Scope(x[2])) # add a special scope here?
            setparent!(scopeof(x[2]), state.scope)
            state(x[2]) # make sure we have bindings etc
            if hasbinding(x[2]) || (is_assignment(x[2]) && hasbinding(x[2][1])) # does expr create a binding
                tls = retrieve_toplevel_scope(x[2])
                expr = hasbinding(x[2]) ? x[2] : x[2][1]
                if isidentifier(bindingof(expr).name)
                    add_binding(expr, state, tls)
                elseif CSTParser.is_exor(bindingof(expr).name)
                    variable_name = parentof(bindingof(expr).name)[2]
                    resolve_ref(variable_name, state.scope, state, [])
                    if hasref(variable_name) && (nameslist = maybeget_listofnames(refof(variable_name))) !== nothing
                        for name in nameslist
                            # Adds Bindings that aren't attached to an expression
                            b = Binding(name, bindingof(expr).val, bindingof(expr).type, [], nothing, nothing)
                            if scopehasbinding(tls, valofid(b.name))
                                b.prev = tls.names[valofid(b.name)]
                                tls.names[valofid(b.name)] = b
                                b.prev.next = b
                            else
                                tls.names[valofid(b.name)] = b
                            end
                        end
                    end
                end
            end
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
            _expr_assert(x[2][3], CSTParser.Begin, 3) && typof(x[2][3][2]) === CSTParser.Block
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
    length(x) == 2 && isidentifier(x[2]) && Symbol(valofid(x[2])) == name && refof(x[2]) == getsymbolserver(state.server)[:Base][Symbol("@", name)]
end

function _points_to_arbitrary_macro(x::EXPR, module_name, name, state)
    length(x) == 2 && isidentifier(x[2]) && valof(x[2]) == name && haskey(getsymbolserver(state.server), Symbol(module_name)) && haskey(getsymbolserver(state.server)[Symbol(module_name)], Symbol("@", name)) && refof(x[2]) == getsymbolserver(state.server)[Symbol(module_name)][Symbol("@", name)]
end

function maybe_eventually_get_id(x::EXPR)
    if isidentifier(x) 
        return x
    elseif typof(x) === CSTParser.InvisBrackets && length(x) == 3
        return maybe_eventually_get_id(x[2])
    end
    return nothing
end
isquoted(x::EXPR) = typof(x) === CSTParser.Quotenode && length(x) == 2 && kindof(x[1]) === CSTParser.Tokens.COLON
maybeget_quotedsymbol(x::EXPR) = isquoted(x) ? maybe_eventually_get_id(x[2]) : nothing
is_loop_iterator(x::EXPR) = typof(x) === BinaryOpCall && length(x) == 3 && (kindof(x[2]) === CSTParser.Tokens.EQ || kindof(x[2]) === CSTParser.Tokens.IN || kindof(x[2]) === CSTParser.Tokens.ELEMENT_OF)

function maybeget_listofnames(b::Binding)
    if is_assignment(b.val) || is_loop_iterator(b.val)
        rhs = b.val[3]
        if (rhsval = maybeget_quotedsymbol(rhs)) !== nothing
            return [rhsval]
        elseif typof(rhs) === CSTParser.Vect || typof(rhs) === CSTParser.TupleH
            names = EXPR[]
            for i = 1:length(rhs)
                CSTParser.ispunctuation(rhs[i]) && continue
                name = maybeget_quotedsymbol(rhs[i])
                if name !== nothing
                    push!(names, name)
                else
                    return nothing
                end
            end
            return names
        end
    end
end
