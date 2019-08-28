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
                CSTParser.setbinding!(x.args[2], x)
                CSTParser.mark_sig_args!(x.args[2])
                s0 = state.scope # store previous scope
                state.scope = Scope(s0, Dict(), nothing, false)
                setscope!(x, state.scope) # tag new scope to generating expression
                state(x.args[2])
                state(x.args[3])
                state.scope = s0
            elseif isidentifier(x.args[2])
                CSTParser.setbinding!(x.args[2], x)
            end
        elseif _points_to_Base_macro(x.args[1], "enum", state)
            for i = 2:length(x.args)
                if !(typof(x.args[i]) === PUNCTUATION)
                    if bindingof(x.args[i]) !== nothing
                        break
                    end
                    if i == 3 && typof(x.args[i]) === CSTParser.Begin
                        for j in 1:length(x.args[i].args[2].args)
                            CSTParser.setbinding!(x.args[i].args[2].args[j], x)
                        end
                        break
                    end
                    CSTParser.setbinding!(x.args[i], x)
                end
            end
        elseif _points_to_Base_macro(x.args[1], "goto", state)
            if length(x.args) == 2 && typof(x.args[2]) === CSTParser.IDENTIFIER
                setref!(x.args[2], NoReference)
            end
        elseif _points_to_Base_macro(x.args[1], "label", state)
            if length(x.args) == 2 && typof(x.args[2]) === CSTParser.IDENTIFIER
                CSTParser.setbinding!(x.args[2])
            end
        # elseif _points_to_Base_macro(x.args[1], "nospecialize", state)
        elseif length(x.args[1].args) == 2 && isidentifier(x.args[1].args[2]) && valof(x.args[1].args[2]) == "nospecialize"
            for i = 2:length(x.args)
                if !(typof(x.args[i]) === PUNCTUATION)
                    if bindingof(x.args[i]) !== nothing
                        break
                    end
                    CSTParser.setbinding!(x.args[i], x)
                end
            end
        end
    end
end


function _points_to_Base_macro(x::EXPR, name, state)
    length(x.args) == 2 && isidentifier(x.args[2]) && valof(x.args[2]) == name && refof(x.args[2]) == getsymbolserver(state.server)["Base"].vals[string("@", name)]
end

function _points_to_arbitrary_macro(x::EXPR, module_name, name, state)
    length(x.args) == 2 && isidentifier(x.args[2]) && valof(x.args[2]) == name && refof(x.args[2]) == getsymbolserver(state.server)[module_name].vals[string("@", name)]
end

