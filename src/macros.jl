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
            if length(x) == 2 && typof(x[2]) === CSTParser.IDENTIFIER
                setref!(x[2], Binding(noname, nothing, nothing, EXPR[], nothing, nothing))
            end
        elseif _points_to_Base_macro(x[1], :label, state)
            if length(x) == 2 && typof(x[2]) === CSTParser.IDENTIFIER
                mark_binding!(x[2])
            end
        elseif length(x[1]) == 2 && isidentifier(x[1][2]) && valof(x[1][2]) == "nospecialize"
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
    if CSTParser.isidentifier(arg) || typof(arg) === CSTParser.Ref
        mark_binding!(_rem_ref(arg))
    elseif is_binary_call(arg, CSTParser.Tokens.EQEQ) || is_binary_call(arg, CSTParser.Tokens.LESS_EQ)  || is_binary_call(arg, CSTParser.Tokens.GREATER_EQ)
        if CSTParser.isidentifier(arg[1]) || typof(arg[1]) === CSTParser.Ref
            mark_binding!(_rem_ref(arg[1]))
        else
            mark_binding!(_rem_ref(arg[3]))
        end
    elseif typof(arg) === CSTParser.Comparison && length(arg) == 5
        mark_binding!(_rem_ref(arg[3]))
    end 
end

function _points_to_Base_macro(x::EXPR, name, state)
    length(x) == 2 && isidentifier(x[2]) && Symbol(valof(x[2])) == name && refof(x[2]) == getsymbolserver(state.server)[:Base][Symbol("@", name)]
end

function _points_to_arbitrary_macro(x::EXPR, module_name, name, state)
    length(x) == 2 && isidentifier(x[2]) && valof(x[2]) == name && haskey(getsymbolserver(state.server), Symbol(module_name)) && haskey(getsymbolserver(state.server)[Symbol(module_name)], Symbol("@", name)) && refof(x[2]) == getsymbolserver(state.server)[Symbol(module_name)][Symbol("@", name)]
end
