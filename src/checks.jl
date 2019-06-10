@enum(LintCodes,IncorrectCallNargs)

function _typeof(x, state)
    if x.typ in (CSTParser.Abstract, CSTParser.Primitive, CSTParser.Struct, CSTParser.Mutable)
        return getsymbolserver(state.server)["Core"].vals["DataType"]
    elseif x.typ in (CSTParser.ModuleH, CSTParser.BareModule)
        return getsymbolserver(state.server)["Core"].vals["Module"]
    elseif x.typ in (CSTParser.ModuleH, CSTParser.BareModule)
        return getsymbolserver["Core"].vals["Module"]
    elseif CSTParser.defines_function(x)
        return return getsymbolserver(state.server)["Core"].vals["Function"]
    end
end

function checks(x)
    check_call_args(x)
end

function check_call_args(x::EXPR)
    if x.typ === Call
        if x.args[1].typ === IDENTIFIER && hasref(x.args[1])
            func = x.args[1].ref
        else
            func = nothing
        end
        if func isa Binding
        elseif func isa SymbolServer.FunctionStore
            nargs = _get_call_nargs(x)
            ok = false
            for m in func.methods
                if nargs == length(m.args)
                    ok = true
                    break
                elseif nargs > length(m.args) && length(m.args) > 0 && endswith(last(m.args)[2], "...") 
                    ok = true
                    break
                end
            end
            if !ok
                x.val = "Error, incorrect number of arguments"
            end
        end
    end
end

function _get_call_nargs(x::EXPR)
    cnt = 0
    for i = 2:length(x.args)
        if x.args[i].typ === PUNCTUATION
        elseif x.args[i].typ === CSTParser.Parameters
            for j = 1:length(x.args[i].args)
                if x.args[i].args[j].typ !== PUNCTUATION
                    cnt += 1
                end
            end
        else
            cnt += 1
        end
    end
    return cnt
end

function _get_top_binding(x::EXPR, name::String)
    if x.scope isa Scope
        return _get_top_binding(x.scope)
    elseif x.parent isa EXPR
        return _get_top_binding(x.parent, name)
    else
        return nothing
    end
end

function _get_top_binding(s::Scope, name::String)
    if haskey(s.names, name)
        return s.names[name]
    elseif s.parent isa Scope
        return _get_top_binding(s.parent, name)
    else
        return nothing
    end
end