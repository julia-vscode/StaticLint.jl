@enum(LintCodes,
MissingRef,
IncorrectCallNargs,
IncorrectIterSpec,
NothingEquality,
NothingNotEq,
ConstIfCondition,
PointlessOR,
PointlessAND,
UnusedBinding,
InvalidTypeDeclaration)

const LintCodeDescriptions = Dict{LintCodes,String}(
    IncorrectCallNargs => "An incorrect number of function arguments has been passed.",
    IncorrectIterSpec => "A loop iterator has been used that will likely error.",
    NothingEquality => "Compare against `nothing` using `===`",
    NothingNotEq => "Compare against `nothing` using `!==`",
    ConstIfCondition => "A boolean literal has been used as the conditional of an if statement - it will either always or never run.",
    PointlessOR => "The first argument of a `||` call is a boolean literal.",
    PointlessAND => "The first argument of a `&&` call is `false`.",
    UnusedBinding => "The variable name has been bound but not used.",
    InvalidTypeDeclaration => "A non-DataType has been used in a type declaration statement."
)

haserror(m::Meta) = m.error !== nothing
haserror(x::EXPR) = hasmeta(x) && haserror(x.meta)
errorof(x::EXPR) = hasmeta(x) ? x.meta.error : nothing
function seterror!(x::EXPR, e)
    if !hasmeta(x)
        x.meta = Meta()
    end
    x.meta.error = e
end


function _typeof(x, state)
    if typof(x) in (CSTParser.Abstract, CSTParser.Primitive, CSTParser.Struct, CSTParser.Mutable)
        return getsymbolserver(state.server)["Core"].vals["DataType"]
    elseif typof(x) in (CSTParser.ModuleH, CSTParser.BareModule)
        return getsymbolserver(state.server)["Core"].vals["Module"]
    elseif CSTParser.defines_function(x)
        return return getsymbolserver(state.server)["Core"].vals["Function"]
    end
end

# Call
function struct_nargs(x::EXPR)
    nargs, ndefaulted_args, params = 0, 0, String[]
    args = typof(x) === CSTParser.Mutable ? x.args[4] : x.args[3]
    inner_constructor = findfirst(a->CSTParser.defines_function(a), args.args)
    if inner_constructor !== nothing
        return func_nargs(args.args[inner_constructor])
    else
        nargs += length(args.args)
    end
    return nargs, ndefaulted_args, params
end

function func_nargs(x::EXPR)
    nargs, ndefaulted_args, params = 0, 0, String[]
    sig = CSTParser.rem_where_decl(CSTParser.get_sig(x))
    if sig.args isa Vector{EXPR}
        for i = 2:length(sig.args)
            if typof(sig.args[i]) === CSTParser.Parameters
                for j = 1:length(sig.args[i])
                    arg = sig.args[i].args[j]
                    if typof(arg) === CSTParser.Kw
                        push!(params, CSTParser.str_value(CSTParser.get_arg_name(arg.args[1])))
                    elseif typof(arg) !== CSTParser.PUNCTUATION
                        # This is wrong
                        nargs += 1
                    end
                end
            else
                
                if typof(sig.args[i]) === CSTParser.Kw
                    ndefaulted_args += 1
                elseif typof(sig.args[i]) !== CSTParser.PUNCTUATION
                    nargs += 1
                end
            end
        end
    else
        nargs = -1
    end
    return nargs, ndefaulted_args, params
end

function call_nargs(x::EXPR)
    nargs, splat, params = 0, 0, String[]
    if x.args isa Vector{EXPR}
        for i = 2:length(x.args)
            if typof(x.args[i]) === CSTParser.Parameters
                for j = 1:length(x.args[i])
                    arg = x.args[i].args[j]
                    if typof(arg) === CSTParser.Kw
                        push!(params, CSTParser.str_value(CSTParser.get_arg_name(arg.args[1])))
                    elseif typof(arg) !== CSTParser.PUNCTUATION
                        # This is wrong
                        nargs += 1
                    end
                end
            else
                arg = x.args[i]
                if typof(arg) === CSTParser.Kw
                    push!(params, CSTParser.str_value(CSTParser.get_arg_name(arg.args[1])))
                elseif typof(arg) !== CSTParser.PUNCTUATION
                    nargs += 1
                    if typof(arg) === CSTParser.UnaryOpCall && kindof(arg.args[2]) === CSTParser.Tokens.DDDOT
                        splat = 1
                    end
                end
            end
        end
    else
        @info string("call_nargs: ", Expr(x))
    end
    
    return nargs, splat, params
end

function func_nargs(m::SymbolServer.MethodStore)
    counts = (0, 0, String[])
    nargs, ndefaulted_args, params = 0, 0, String[]
    for a in m.args
        if last(a) == ".KW"
            push!(params, first(a))
        elseif startswith(last(a), "Vararg") || endswith(first(a), "...") || endswith(last(a), "...")
            ndefaulted_args += Inf
        else
            nargs += 1
        end
    end
    return nargs, ndefaulted_args, params
end


compare_f_call(m_counts, call_counts) = m_counts[1] <= call_counts[1] <= m_counts[1] + m_counts[2] && length(call_counts[3]) <= length(m_counts[3]) && all(kw in m_counts[3] for kw in call_counts[3])

function check_call(x, server)
    if typof(x) === Call
        if typof(first(x.args)) === IDENTIFIER && hasref(first(x.args))
            func_ref = refof(first(x.args))
        elseif typof(first(x)) === BinaryOpCall && kindof(first(x).args[2]) === CSTParser.Tokens.DOT && typof(first(last(first(x)))) === IDENTIFIER && hasref(first(last(first(x))))
            func_ref = refof(first(last(first(x.args).args)))
        else
            return
        end
        
        if func_ref isa SymbolServer.FunctionStore || func_ref isa SymbolServer.DataTypeStore
            call_counts = call_nargs(x)
            for m in func_ref.methods
                m_counts = func_nargs(m)
                if compare_f_call(m_counts, call_counts)
                    return
                end
            end
            seterror!(x, IncorrectCallNargs)
        elseif func_ref isa Binding && (func_ref.type === getsymbolserver(server)["Core"].vals["Function"] || func_ref.type === getsymbolserver(server)["Core"].vals["DataType"])
            call_counts = call_nargs(x)
            b = func_ref
            while b.next isa Binding && b.next.type == getsymbolserver(server)["Core"].vals["Function"]
                b = b.next
            end
            while true
                if b.type == getsymbolserver(server)["Core"].vals["Function"]
                    m_counts = func_nargs(b.val)
                elseif b.type == getsymbolserver(server)["Core"].vals["DataType"]
                    m_counts = struct_nargs(b.val)
                elseif b.val isa SymbolServer.FunctionStore || b.val isa SymbolServer.DataTypeStore
                    for m in b.val.methods
                        m_counts = func_nargs(m)
                        if compare_f_call(m_counts, call_counts)
                            return
                        end
                    end
                    break
                else
                    break
                end
                if compare_f_call(m_counts, call_counts)
                    return
                elseif CSTParser.rem_where_decl(CSTParser.get_sig(b.val)) == x
                    return
                end
                b.prev === nothing && break
                b = b.prev
            end
            seterror!(x, IncorrectCallNargs)
        end
    end
end

function check_loop_iter(x::EXPR, server)
    if typof(x) === CSTParser.For
        if length(x.args) > 1 && typof(x.args[2]) === CSTParser.BinaryOpCall && refof(x.args[2]) === nothing
            rng = x.args[2].args[3]
            if typof(rng) === CSTParser.LITERAL && kindof(rng) == CSTParser.Tokens.FLOAT || kindof(rng) == CSTParser.Tokens.INTEGER
                seterror!(x.args[2], IncorrectIterSpec)
            elseif typof(rng) === CSTParser.Call && refof(rng.args[1]) === getsymbolserver(server)["Base"].vals["length"]
                seterror!(x.args[2], IncorrectIterSpec)
            end
        end
    elseif typof(x) === CSTParser.Generator
        for i = 3:length(x.args)
            if typof(x.args[i]) === CSTParser.BinaryOpCall && refof(x.args[i]) === nothing
                rng = x.args[i].args[3]
                if typof(rng) === CSTParser.LITERAL && kindof(rng) == CSTParser.Tokens.FLOAT || kindof(rng) == CSTParser.Tokens.INTEGER
                    seterror!(x.args[i], IncorrectIterSpec)
                elseif typof(rng) === CSTParser.Call && valof(rng.args[1]) == "length" && refof(rng.args[1]) === getsymbolserver(server)["Base"].vals["length"]
                    seterror!(x.args[i], IncorrectIterSpec)
                end
            end
        end
    end
end

function check_nothing_equality(x::EXPR, server)
    if typof(x) === CSTParser.BinaryOpCall
        if kindof(x.args[2]) === CSTParser.Tokens.EQEQ && valof(x.args[3]) == "nothing" && refof(x.args[3]) === getsymbolserver(server)["Core"].vals["nothing"]
            seterror!(x.args[2], NothingEquality)
        elseif kindof(x.args[2]) === CSTParser.Tokens.NOT_EQ && valof(x.args[3]) == "nothing" && refof(x.args[3]) === getsymbolserver(server)["Core"].vals["nothing"]
            seterror!(x.args[2], NothingNotEq)
        end
    end
end

function _get_call_nargs(x::EXPR)
    cnt = 0
    kws = 0
    for i = 2:length(x.args)
        if typof(x.args[i]) === PUNCTUATION
        elseif typof(x.args[i]) === CSTParser.Parameters
            for j = 1:length(x.args[i].args)
                if typof(x.args[i].args[j]) !== PUNCTUATION
                    kws += 1
                end
            end
        elseif typof(x.args[i]) === CSTParser.Kw
            kws += 1
        else
            cnt += 1
        end
    end
    return cnt, kws
end

function _get_top_binding(x::EXPR, name::String)
    if scopeof(x) isa Scope
        return _get_top_binding(scopeof(x), name)
    elseif parentof(x) isa EXPR
        return _get_top_binding(parentof(x), name)
    else
        return nothing
    end
end
# Given the name of a function binding lookup the last declared method (i.e. the one 
# stored in the scope)
_get_last_method(x, b::Binding, server) = b

function _get_last_method(x::EXPR, b::Binding, server)
    if scopeof(x) isa Scope
        if haskey(scopeof(x).names, b.name)
            if scopeof(x).names[b.name] isa Binding && scopeof(x).names[b.name].type == b.type
                return scopeof(x).names[b.name]
            end
        end
    elseif parentof(x) isa EXPR
        return _get_last_method(parentof(x), b.name, server)
    end
    return b
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

function check_if_conds(x::EXPR)
    if typof(x) === CSTParser.If && length(x.args) > 2 
        cond = typof(first(x.args)) == CSTParser.KEYWORD ? x.args[2] : x.args[1]
        if typof(cond) === CSTParser.LITERAL && (kindof(cond) === CSTParser.Tokens.TRUE || kindof(cond) === CSTParser.Tokens.FALSE)
            seterror!(cond, ConstIfCondition)
        end
    end
end

function check_lazy(x::EXPR)
    if typof(x) === CSTParser.BinaryOpCall
        if kindof(x.args[2]) === CSTParser.Tokens.LAZY_OR
            if (typof(x.args[1]) === CSTParser.LITERAL && (kindof(x.args[1]) === CSTParser.Tokens.TRUE || kindof(x.args[1]) === CSTParser.Tokens.FALSE))
                seterror!(x, PointlessOR)
            end
        elseif kindof(x.args[2]) === CSTParser.Tokens.LAZY_AND
            if (typof(x.args[1]) === CSTParser.LITERAL && kindof(x.args[1]) === CSTParser.Tokens.FALSE) || (typof(x.args[3]) === CSTParser.LITERAL && kindof(x.args[3]) === CSTParser.Tokens.FALSE)
                seterror!(x, PointlessAND)
            end
        end
    end
end

function check_is_callable(x::EXPR, server)
    if typof(x) === CSTParser.Call
        func = first(x.args)

        if hasref(func)
        end
    end    
end

function check_datatype_decl(x::EXPR, server)
    # Only call in function signatures
    if typof(x) === CSTParser.BinaryOpCall && length(x.args) === 3 && kindof(x.args[2]) === CSTParser.Tokens.DECLARATION && 
        parentof(x) isa EXPR && typof(parentof(x)) === CSTParser.Call
        if hasref(last(x.args))
            dt = refof(last(x.args))
            if dt isa SymbolServer.DataTypeStore || dt isa Binding && dt.val isa SymbolServer.DataTypeStore
            elseif dt isa Binding && dt.type !== nothing
                safety_trip = 0
                while dt.type == getsymbolserver(server)["Core"].vals["Function"]
                    safety_trip += 1
                    dt.prev === nothing && break
                    dt = dt.prev
                    if safety_trip > 50 
                        @warn string(Expr(dt.name))
                        return
                    end
                end
                if dt.type !== nothing && dt.type !== getsymbolserver(server)["Core"].vals["DataType"]
                    seterror!(x, InvalidTypeDeclaration)
                end
            end
        elseif typof(last(x.args)) === CSTParser.LITERAL
            seterror!(x, InvalidTypeDeclaration)
        end
    end    
end


mutable struct LintOptions
    call::Bool
    iter::Bool
    nothingcomp::Bool
    constif::Bool
    lazy::Bool
    datadecl::Bool
end
LintOptions() = LintOptions(true, true, true, true, true, true)

function check_all(x::EXPR, opts::LintOptions, server)
    # Do checks
    opts.call && check_call(x, server)
    opts.iter && check_loop_iter(x, server)
    opts.nothingcomp && check_nothing_equality(x, server)
    opts.constif && check_if_conds(x)
    opts.lazy && check_lazy(x)
    # check_is_callable(x, server)
    opts.datadecl && check_datatype_decl(x, server)
    if x.args !== nothing
        for i in 1:length(x.args)
            check_all(x.args[i], opts, server)
        end
    end
end


function collect_hints(x::EXPR, missing = true, isquoted = false, errs = Tuple{Int,EXPR}[], pos = 0)
    if quoted(x)
        isquoted = true
    elseif isquoted && unquoted(x)
        isquoted = false
    end
    if typof(x) === CSTParser.ErrorToken 
        # collect parse errors
        push!(errs, (pos, x))
    elseif !isquoted
        if missing && CSTParser.isidentifier(x) && !hasref(x)
            push!(errs, (pos, x))
        elseif haserror(x) && errorof(x) isa StaticLint.LintCodes
            # collect lint hints
            push!(errs, (pos, x))
        end
    end
    
    if x.args !== nothing
        for i in 1:length(x.args)
            collect_hints(x.args[i], missing, isquoted, errs, pos)
            pos += x.args[i].fullspan
        end
    end
    errs
end


