@enum(LintCodes,IncorrectCallNargs,IncorrectIterSpec,NothingEquality,NothingNotEq)

function _typeof(x, state)
    if typof(x) in (CSTParser.Abstract, CSTParser.Primitive, CSTParser.Struct, CSTParser.Mutable)
        return getsymbolserver(state.server)["Core"].vals["DataType"]
    elseif typof(x) in (CSTParser.ModuleH, CSTParser.BareModule)
        return getsymbolserver(state.server)["Core"].vals["Module"]
    elseif typof(x) in (CSTParser.ModuleH, CSTParser.BareModule)
        return getsymbolserver["Core"].vals["Module"]
    elseif CSTParser.defines_function(x)
        return return getsymbolserver(state.server)["Core"].vals["Function"]
    end
end

function checks(x, server)
    # check_call_args(x)
    check_loop_iter(x, server)
    check_nothing_equality(x, server)
end

function check_call_args(x::EXPR)
    if typof(x) === Call
        if typof(x.args[1]) === IDENTIFIER && hasref(x.args[1])
            func = refof(x.args[1])
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
                setref!(x, IncorrectCallNargs)
            end
        end
    end
end

function check_loop_iter(x::EXPR, server)
    if typof(x) === CSTParser.For
        if length(x.args) > 1 && typof(x.args[2]) === CSTParser.BinaryOpCall && refof(x.args[2]) === nothing
            rng = x.args[2].args[3]
            if typof(rng) === CSTParser.LITERAL && kindof(rng) == CSTParser.Tokens.FLOAT || kindof(rng) == CSTParser.Tokens.INTEGER
                setref!(x.args[2], IncorrectIterSpec)
            elseif typof(rng) === CSTParser.Call && refof(rng.args[1]) === getsymbolserver(server)["Base"].vals["length"]
                setref!(x.args[2], IncorrectIterSpec)
            end
        end
    elseif typof(x) === CSTParser.Generator
        for i = 3:length(x.args)
            if typof(x.args[i]) === CSTParser.BinaryOpCall && refof(x.args[i]) === nothing
                rng = x.args[i].args[3]
                if typof(rng) === CSTParser.LITERAL && kindof(rng) == CSTParser.Tokens.FLOAT || kindof(rng) == CSTParser.Tokens.INTEGER
                    setref!(x.args[i], IncorrectIterSpec)
                elseif typof(rng) === CSTParser.Call && valof(rng.args[1]) == "length" && refof(rng.args[1]) === getsymbolserver(server)["Base"].vals["length"]
                    setref!(x.args[i], IncorrectIterSpec)
                end
            end
        end
    end
end

function check_nothing_equality(x::EXPR, server)
    if typof(x) === CSTParser.BinaryOpCall
        if kindof(x.args[2]) === CSTParser.Tokens.EQEQ && valof(x.args[3]) == "nothing" && refof(x.args[3]) === getsymbolserver(server)["Core"].vals["nothing"]
            setref!(x.args[2], NothingEquality)
        elseif kindof(x.args[2]) === CSTParser.Tokens.NOT_EQ && valof(x.args[3]) == "nothing" && refof(x.args[3]) === getsymbolserver(server)["Core"].vals["nothing"]
            setref!(x.args[2], NothingNotEq)
        end
    end
end

function _get_call_nargs(x::EXPR)
    cnt = 0
    for i = 2:length(x.args)
        if typof(x.args[i]) === PUNCTUATION
        elseif typof(x.args[i]) === CSTParser.Parameters
            for j = 1:length(x.args[i].args)
                if typof(x.args[i].args[j]) !== PUNCTUATION
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
    if scopeof(x) isa Scope
        return _get_top_binding(scopeof(x))
    elseif parentof(x) isa EXPR
        return _get_top_binding(parentof(x), name)
    else
        return nothing
    end
end

function _get_top_binding(s::Scope, name::String)
    if haskey(s.names, name)
        return s.names[name]
    elseif parentof(s) isa Scope
        return _get_top_binding(parentof(s), name)
    else
        return nothing
    end
end

function _get_global_scope(s::Scope)
    if !s.ismodule && parentof(s) isa Scope && parentof(s) != s
        return _get_global_scope(parentof(s))
    else
        return s
    end
end
