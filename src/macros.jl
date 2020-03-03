function handle_macro(@nospecialize(x), state) end
function handle_macro(x::EXPR, state)
    typof(x) !== MacroCall && return
    if typof(x.args[1]) === MacroName
        state(x.args[1])
        if _points_to_Base_macro(x.args[1], "deprecate", state) && length(x.args) == 3
            if bindingof(x.args[2]) !== nothing
                return
            elseif CSTParser.is_func_call(x.args[2])
                # add deprecated method
                # add deprecated function binding and args in new scope
                mark_binding!(x.args[2], x)
                mark_sig_args!(x.args[2])
                s0 = state.scope # store previous scope
                state.scope = Scope(s0, x, Dict(), nothing, false)
                setscope!(x, state.scope) # tag new scope to generating expression
                state(x.args[2])
                state(x.args[3])
                state.scope = s0
            elseif isidentifier(x.args[2])
                mark_binding!(x.args[2], x)
            end
        elseif _points_to_Base_macro(x.args[1], "enum", state)
            for i = 2:length(x.args)
                if !(typof(x.args[i]) === PUNCTUATION)
                    if bindingof(x.args[i]) !== nothing
                        break
                    end
                    if i == 3 && typof(x.args[i]) === CSTParser.Begin
                        for j in 1:length(x.args[i].args[2].args)
                            mark_binding!(x.args[i].args[2].args[j], x)
                        end
                        break
                    end
                    mark_binding!(x.args[i], x)
                end
            end
        elseif _points_to_Base_macro(x.args[1], "goto", state)
            if length(x.args) == 2 && typof(x.args[2]) === CSTParser.IDENTIFIER
                setref!(x.args[2], Binding(noname, nothing, nothing, EXPR[], nothing, nothing))
            end
        elseif _points_to_Base_macro(x.args[1], "label", state)
            if length(x.args) == 2 && typof(x.args[2]) === CSTParser.IDENTIFIER
                mark_binding!(x.args[2])
            end
        # elseif _points_to_Base_macro(x.args[1], "nospecialize", state)
        elseif length(x.args[1].args) == 2 && isidentifier(x.args[1].args[2]) && valof(x.args[1].args[2]) == "nospecialize"
            for i = 2:length(x.args)
                if !(typof(x.args[i]) === PUNCTUATION)
                    if bindingof(x.args[i]) !== nothing
                        break
                    end
                    mark_binding!(x.args[i], x)
                end
            end
        elseif _points_to_arbitrary_macro(x.args[1], "Turing", "model", state) && length(x.args) == 2 && 
            _binary_assert(x.args[2], CSTParser.Tokens.EQ) && 
            _expr_assert(x.args[2].args[3], CSTParser.Begin, 3) && typof(x.args[2].args[3].args[2]) === CSTParser.Block && x.args[2].args[3].args[2].args isa Vector{EXPR}
            for i = 1:length(x[2][3][2].args)
                ex = x[2][3][2][i]
                if typof(ex) == CSTParser.BinaryOpCall && kindof(ex[2]) === CSTParser.Tokens.APPROX
                    mark_binding!(ex)
                end
            end
        elseif _points_to_arbitrary_macro(x.args[1], "JuMP", "variable", state)
            if length(x.args) < 3
                return
            elseif length(x.args) >= 5 && typof(x.args[2]) === PUNCTUATION
                _mark_JuMP_binding(x.args[5])
            else
                _mark_JuMP_binding(x.args[3])
            end
        elseif (_points_to_arbitrary_macro(x.args[1], "JuMP", "expression", state) || 
            _points_to_arbitrary_macro(x.args[1], "JuMP", "NLexpression", state) ||
            _points_to_arbitrary_macro(x.args[1], "JuMP", "constraint", state) || _points_to_arbitrary_macro(x.args[1], "JuMP", "NLconstraint", state)) && length(x.args) > 1
            if typof(x.args[2]) === PUNCTUATION 
                if length(x.args) == 8
                    _mark_JuMP_binding(x.args[5])
                end
            else
                if length(x.args) == 4
                    _mark_JuMP_binding(x.args[3])
                end
            end
        end
    elseif typof(x.args[1]) == CSTParser.GlobalRefDoc && length(x.args) == 3 && CSTParser.isliteral(x.args[2]) && kindof(x.args[2]) === CSTParser.Tokens.TRIPLE_STRING && isidentifier(x.args[3])
        mark_binding!(x.args[3])
        setref!(x.args[3], bindingof(x.args[3]))
    end
end

function _rem_ref(x::EXPR)
    if typof(x) === CSTParser.Ref && x.args isa Vector{EXPR} && length(x.args) > 0
        return x.args[1]
    end
    return x
end

function _mark_JuMP_binding(arg)
    if CSTParser.isidentifier(arg) || typof(arg) === CSTParser.Ref
        mark_binding!(_rem_ref(arg))
    elseif _binary_assert(arg, CSTParser.Tokens.EQEQ) || _binary_assert(arg, CSTParser.Tokens.LESS_EQ)  || _binary_assert(arg, CSTParser.Tokens.GREATER_EQ)
        if CSTParser.isidentifier(arg.args[1]) || typof(arg.args[1]) === CSTParser.Ref
            mark_binding!(_rem_ref(arg.args[1]))
        else
            mark_binding!(_rem_ref(arg.args[3]))
        end
    elseif typof(arg) === CSTParser.Comparison && arg.args isa Vector{EXPR} && length(arg.args) == 5
        mark_binding!(_rem_ref(arg.args[3]))
    end 
end


function _points_to_Base_macro(x::EXPR, name, state)
    length(x.args) == 2 && isidentifier(x.args[2]) && valof(x.args[2]) == name && refof(x.args[2]) == getsymbolserver(state.server)["Base"].vals[string("@", name)]
end

function _points_to_arbitrary_macro(x::EXPR, module_name, name, state)
    length(x.args) == 2 && isidentifier(x.args[2]) && valof(x.args[2]) == name && haskey(getsymbolserver(state.server), module_name) && haskey(getsymbolserver(state.server)[module_name].vals, string("@", name)) && refof(x.args[2]) == getsymbolserver(state.server)[module_name].vals[string("@", name)]
end
