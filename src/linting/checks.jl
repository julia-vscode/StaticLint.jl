@enum(LintCodes,
MissingRef,
IncorrectCallArgs,
IncorrectIterSpec,
NothingEquality,
NothingNotEq,
ConstIfCondition,
EqInIfConditional,
PointlessOR,
PointlessAND,
UnusedBinding,
InvalidTypeDeclaration,
UnusedTypeParameter,
IncludeLoop,
MissingFile,
InvalidModuleName,
TypePiracy)

const LintCodeDescriptions = Dict{LintCodes,String}(IncorrectCallArgs => "Possible method call error.",
    IncorrectIterSpec => "A loop iterator has been used that will likely error.",
    NothingEquality => "Compare against `nothing` using `===`",
    NothingNotEq => "Compare against `nothing` using `!==`",
    ConstIfCondition => "A boolean literal has been used as the conditional of an if statement - it will either always or never run.",
    EqInIfConditional => "Unbracketed assignment in if conditional statements is not allowed, did you mean to use ==?",
    PointlessOR => "The first argument of a `||` call is a boolean literal.",
    PointlessAND => "The first argument of a `&&` call is `false`.",
    UnusedBinding => "The variable name has been bound but not used.",
    InvalidTypeDeclaration => "A non-DataType has been used in a type declaration statement.",
    UnusedTypeParameter => "A DataType parameter has been specified but not used.",
    IncludeLoop => "Loop detected, this file has already been included.",
    MissingFile => "The included file can not be found.",
    InvalidModuleName => "Module name matches that of its parent.",
    TypePiracy => "An imported function has been extended without using module defined typed arguments.")

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
    if x isa EXPR
        if typof(x) in (CSTParser.Abstract, CSTParser.Primitive, CSTParser.Struct, CSTParser.Mutable)
            return CoreTypes.DataType
        elseif typof(x) in (CSTParser.ModuleH, CSTParser.BareModule)
            return CoreTypes.Module
        elseif CSTParser.defines_function(x)
            return CoreTypes.Function
        end
    elseif x isa SymbolServer.DataTypeStore
        return CoreTypes.DataType
    elseif x isa SymbolServer.FunctionStore
        return CoreTypes.Function
    end
end

# Call
function struct_nargs(x::EXPR)
    # struct defs wrapped in macros are likely to have some arbirtary additional constructors, so lets allow anything
    parentof(x) isa EXPR && typof(parentof(x)) === CSTParser.MacroCall && return 0, typemax(Int), Symbol[], true
    minargs, maxargs, kws, kwsplat = 0, 0, Symbol[], false
    args = typof(x) === CSTParser.Mutable ? x[4] : x[3]
    length(args) == 0 && return 0, typemax(Int), kws, kwsplat
    inner_constructor = findfirst(a->CSTParser.defines_function(a), args.args)
    if inner_constructor !== nothing
        return func_nargs(args[inner_constructor])
    else
        minargs = maxargs = length(args)
    end
    return minargs, maxargs, kws, kwsplat
end

function func_nargs(x::EXPR)
    minargs, maxargs, kws, kwsplat = 0, 0, Symbol[], false
    sig = CSTParser.rem_where_decl(CSTParser.get_sig(x))
    for i = 2:length(sig)
        arg = sig[i]
        if typof(arg) === CSTParser.MacroCall && length(arg) > 1 &&
            _expr_assert(arg[1], MacroName, 2) && valof(arg[1][2]) == "nospecialize"
            if length(arg) == 2
                arg = arg[2]
            end
        end
        if typof(arg) === CSTParser.PUNCTUATION
            # skip
        elseif typof(arg) === CSTParser.Parameters
            for j = 1:length(arg)
                arg1 = arg[j]
                if typof(arg1) === CSTParser.Kw
                    push!(kws, Symbol(CSTParser.str_value(CSTParser.get_arg_name(arg1[1]))))
                elseif typof(arg1) === CSTParser.BinaryOpCall && kindof(arg1[2]) === CSTParser.Tokens.DDDOT
                    kwsplat = true
                end
            end
        elseif typof(arg) === CSTParser.Kw
            if typof(arg[1]) === UnaryOpCall && kindof(arg[1][2]) === CSTParser.Tokens.DDDOT
                maxargs = typemax(Int)
            else
                maxargs !== typemax(Int) && (maxargs += 1)
            end
        elseif (typof(arg) === UnaryOpCall && kindof(arg[2]) === CSTParser.Tokens.DDDOT) ||
            (_binary_assert(arg, CSTParser.Tokens.DECLARATION) &&
            ((typof(arg[3]) === CSTParser.IDENTIFIER && valof(arg[3]) == "Vararg") ||
            (typof(arg[3]) === CSTParser.Curly && typof(arg[3][1]) === CSTParser.IDENTIFIER && valof(arg[3][1]) == "Vararg")))
            maxargs = typemax(Int)
        else
            minargs += 1
            maxargs !== typemax(Int) && (maxargs += 1)
        end
    end

    return minargs, maxargs, kws, kwsplat
end

function func_nargs(m::SymbolServer.MethodStore)
    minargs, maxargs, kws, kwsplat = 0, 0, Symbol[], false

    for arg in m.sig
        if CoreTypes.isva(last(arg))
            maxargs = typemax(Int)
        else
            minargs += 1
            maxargs !== typemax(Int) && (maxargs += 1)
        end
    end
    for kw in m.kws
        if endswith(String(kw), "...")
            kwsplat = true
        else
            push!(kws, kw)
        end
    end
    return minargs, maxargs, kws, kwsplat
end

function call_nargs(x::EXPR)
    minargs, maxargs, kws = 0, 0, Symbol[]
    if length(x) > 0
        for i = 2:length(x)
            arg = x[i]
            if typof(arg) === CSTParser.PUNCTUATION
                # skip
            elseif typof(x[i]) === CSTParser.Parameters
                for j = 1:length(x[i])
                    arg = x[i][j]
                    if typof(arg) === CSTParser.Kw
                        push!(kws, Symbol(CSTParser.str_value(CSTParser.get_arg_name(arg[1]))))
                    end
                end
            elseif typof(arg) === CSTParser.Kw
                push!(kws, Symbol(CSTParser.str_value(CSTParser.get_arg_name(arg[1]))))
            elseif typof(arg) === CSTParser.UnaryOpCall && kindof(arg[2]) === CSTParser.Tokens.DDDOT
                maxargs = typemax(Int)
            else
                minargs += 1
                maxargs !== typemax(Int) && (maxargs += 1)
            end
        end
    else
        @info string("call_nargs: ", Expr(x))
    end

    return minargs, maxargs, kws
end

# compare_f_call(m_counts, call_counts) = true # fallback method

function compare_f_call(m_counts::Tuple{Int,Int,Array{Symbol},Bool}, call_counts::Tuple{Int,Int,Array{Symbol}})
    if call_counts[2] == typemax(Int)
        call_counts[1] <= call_counts[2] < m_counts[1] && return false
    else
        !(m_counts[1] <= call_counts[1] <= call_counts[2] <= m_counts[2]) && return false
    end
    if !m_counts[4] # no splatted kw in method sig
        length(call_counts[3]) > length(m_counts[3]) && return false # call has more kws than method accepts
        !all(kw in m_counts[3] for kw in call_counts[3]) && return false # call supplies a kw that isn't defined in the method
    else # splatted kw in method so accept any kw in call
    end
    return true
end

function check_call(x, server)
    if typof(x) === Call
        parentof(x) isa EXPR && typof(parentof(x)) === CSTParser.Do && return # TODO: add number of args specified in do block.
        length(x) == 0 && return
        if typof(first(x)) === IDENTIFIER && hasref(first(x))
            func_ref = refof(first(x))
        elseif _binary_assert(x[1], CSTParser.Tokens.DOT) && typof(x[1]) === CSTParser.Quotenode && length(x[1][3]) > 0 && typof(x[1][3][1]) === IDENTIFIER && hasref(first(x)[3][1])
            func_ref = refof(first(last(first(x))))
        else
            return
        end
        if func_ref isa SymbolServer.FunctionStore || func_ref isa SymbolServer.DataTypeStore
            call_counts = call_nargs(x)
            function ff(m)
                m_counts = func_nargs(m)
                return compare_f_call(m_counts, call_counts)
            end
            tls = retrieve_toplevel_scope(x)
            tls == nothing && return
            iterate_over_ss_methods(func_ref, tls, server, ff) && return # returns if ff(m) == true for any methods
            seterror!(x, IncorrectCallArgs)
        elseif func_ref isa Binding && (func_ref.type === CoreTypes.Function || func_ref.type === CoreTypes.DataType)
            call_counts = call_nargs(x)
            function ff1(m)
                m_counts = func_nargs(m)
                return compare_f_call(m_counts, call_counts)
            end
            b = func_ref
            seen = Binding[]
            while b.next isa Binding && b.next.type == CoreTypes.Function && !(b in seen)
                push!(seen, b)
                b = b.next
            end
            seen = Binding[]
            while true
                b in seen && break
                if !(b isa Binding) # Needs to be cleaned up
                    if b isa SymbolServer.FunctionStore || b isa SymbolServer.DataTypeStore
                        tls = retrieve_toplevel_scope(x)
                        tls == nothing && return
                        iterate_over_ss_methods(b, tls, server, ff1) && return
                        break
                    else
                        return
                    end
                elseif b.type == CoreTypes.Function && b.val isa EXPR
                    m_counts = func_nargs(b.val)
                elseif b.type == CoreTypes.DataType && b.val isa EXPR && CSTParser.defines_struct(b.val)
                    m_counts = struct_nargs(b.val)
                elseif b.val isa SymbolServer.FunctionStore || b.val isa SymbolServer.DataTypeStore
                    tls = retrieve_toplevel_scope(x)
                    tls == nothing && return
                    iterate_over_ss_methods(b.val, tls, server, ff1) && return
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
                b in seen && break
                push!(seen, b)
                b = b.prev
            end
            seterror!(x, IncorrectCallArgs)
        end
    end
end

function check_loop_iter(x::EXPR, server)
    if typof(x) === CSTParser.For
        if length(x) > 1 && typof(x[2]) === CSTParser.BinaryOpCall && refof(x[2]) === nothing
            rng = x[2][3]
            if typof(rng) === CSTParser.LITERAL && kindof(rng) == CSTParser.Tokens.FLOAT || kindof(rng) == CSTParser.Tokens.INTEGER
                seterror!(x[2], IncorrectIterSpec)
            elseif typof(rng) === CSTParser.Call && refof(rng[1]) === getsymbolserver(server)[:Base][:length]
                seterror!(x[2], IncorrectIterSpec)
            end
        end
    elseif typof(x) === CSTParser.Generator
        for i = 3:length(x)
            if typof(x[i]) === CSTParser.BinaryOpCall && refof(x[i]) === nothing
                rng = x[i][3]
                if typof(rng) === CSTParser.LITERAL && kindof(rng) == CSTParser.Tokens.FLOAT || kindof(rng) == CSTParser.Tokens.INTEGER
                    seterror!(x[i], IncorrectIterSpec)
                elseif typof(rng) === CSTParser.Call && valof(rng[1]) == "length" && refof(rng[1]) === getsymbolserver(server)[:Base][:length]
                    seterror!(x[i], IncorrectIterSpec)
                end
            end
        end
    end
end

function check_nothing_equality(x::EXPR, server)
    if typof(x) === CSTParser.BinaryOpCall
        if kindof(x[2]) === CSTParser.Tokens.EQEQ && valof(x[3]) == "nothing" && refof(x[3]) === getsymbolserver(server)[:Core][:nothing]
            seterror!(x[2], NothingEquality)
        elseif kindof(x[2]) === CSTParser.Tokens.NOT_EQ && valof(x[3]) == "nothing" && refof(x[3]) === getsymbolserver(server)[:Core][:nothing]
            seterror!(x[2], NothingNotEq)
        end
    end
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
        if scopehasbinding(scopeof(x), b.name)
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
    if scopehasbinding(s, name)
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
    if typof(x) === CSTParser.If && length(x) > 2
        cond = typof(first(x)) == CSTParser.KEYWORD ? x[2] : x[1]
        if typof(cond) === CSTParser.LITERAL && (kindof(cond) === CSTParser.Tokens.TRUE || kindof(cond) === CSTParser.Tokens.FALSE)
            seterror!(cond, ConstIfCondition)
        elseif _binary_assert(cond, CSTParser.Tokens.EQ)
            seterror!(cond, EqInIfConditional)
        end
    end
end

function check_lazy(x::EXPR)
    if typof(x) === CSTParser.BinaryOpCall
        if kindof(x[2]) === CSTParser.Tokens.LAZY_OR
            if (typof(x[1]) === CSTParser.LITERAL && (kindof(x[1]) === CSTParser.Tokens.TRUE || kindof(x[1]) === CSTParser.Tokens.FALSE))
                seterror!(x, PointlessOR)
            end
        elseif kindof(x[2]) === CSTParser.Tokens.LAZY_AND
            if (typof(x[1]) === CSTParser.LITERAL && kindof(x[1]) === CSTParser.Tokens.FALSE) || (typof(x[3]) === CSTParser.LITERAL && kindof(x[3]) === CSTParser.Tokens.FALSE)
                seterror!(x, PointlessAND)
            end
        end
    end
end

function check_is_callable(x::EXPR, server)
    if typof(x) === CSTParser.Call
        func = first(x)

        if hasref(func)
        end
    end
end

function check_datatype_decl(x::EXPR, server)
    # Only call in function signatures
    if typof(x) === CSTParser.BinaryOpCall && length(x) === 3 && kindof(x[2]) === CSTParser.Tokens.DECLARATION &&
        parentof(x) isa EXPR && typof(parentof(x)) === CSTParser.Call
        if hasref(last(x))
            dt = refof(last(x))
            if dt isa SymbolServer.DataTypeStore || dt isa Binding && dt.val isa SymbolServer.DataTypeStore
            elseif dt isa Binding && dt.type !== nothing
                safety_trip = 0
                while dt.type == CoreTypes.Function
                    safety_trip += 1
                    dt.prev === nothing && break
                    dt = dt.prev
                    if safety_trip > 50
                        @warn string(Expr(dt.name))
                        return
                    end
                end
                if dt.type !== nothing && dt.type !== CoreTypes.DataType
                    seterror!(x, InvalidTypeDeclaration)
                end
            end
        elseif typof(last(x)) === CSTParser.LITERAL
            seterror!(x, InvalidTypeDeclaration)
        end
    end
end

function check_modulename(x::EXPR)
    if (typof(x) === CSTParser.ModuleH || typof(x) === CSTParser.BareModule) && # x is a module
        scopeof(x) isa Scope && parentof(scopeof(x)) isa Scope && # it has a scope and a parent scope
        (typof(parentof(scopeof(x)).expr) === CSTParser.ModuleH ||
        typof(parentof(scopeof(x)).expr) === CSTParser.BareModule) && # the parent scope is a module
        valof(CSTParser.get_name(x)) == valof(CSTParser.get_name(parentof(scopeof(x)).expr)) # their names match
        seterror!(CSTParser.get_name(x), InvalidModuleName)
    end
end


mutable struct LintOptions
    call::Bool
    iter::Bool
    nothingcomp::Bool
    constif::Bool
    lazy::Bool
    datadecl::Bool
    typeparam::Bool
    modname::Bool
    pirates::Bool
end
LintOptions() = LintOptions(true, true, true, true, true, false, true, true, true)

function check_all(x::EXPR, opts::LintOptions, server)
    # Do checks
    opts.call && check_call(x, server)
    opts.iter && check_loop_iter(x, server)
    opts.nothingcomp && check_nothing_equality(x, server)
    opts.constif && check_if_conds(x)
    opts.lazy && check_lazy(x)
    # check_is_callable(x, server)
    opts.datadecl && check_datatype_decl(x, server)
    opts.typeparam && check_typeparams(x)
    opts.modname && check_modulename(x)
    opts.pirates && check_for_pirates(x)
    for i in 1:length(x)
        check_all(x[i], opts, server)
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
        if missing && CSTParser.isidentifier(x) && !hasref(x) &&
            !(valof(x) == "var" && parentof(x) isa EXPR && typof(parentof(x)) === CSTParser.NONSTDIDENTIFIER) &&
            !((valof(x) == "stdcall" || valof(x) == "cdecl" || valof(x) == "fastcall" || valof(x) == "thiscall" || valof(x) == "llvmcall") && is_in_fexpr(x, x->typof(x) === CSTParser.Call && isidentifier(x[1]) && valof(x[1]) == "ccall"))
            push!(errs, (pos, x))
        elseif haserror(x) && errorof(x) isa StaticLint.LintCodes
            # collect lint hints
            push!(errs, (pos, x))
        end
    end
    

    for i in 1:length(x)
        collect_hints(x[i], missing, isquoted, errs, pos)
        pos += x[i].fullspan
    end

    errs
end

function check_typeparams(x::EXPR)
    if typof(x) === CSTParser.WhereOpCall
        for i = 3:length(x)
            if hasbinding(x[i])
                if !(bindingof(x[i]).refs isa Vector)
                    seterror!(x[i], UnusedTypeParameter)
                elseif length(bindingof(x[i]).refs) == 1
                    # there should (will?) always be at least one reference in the where declaration
                    seterror!(x[i], UnusedTypeParameter)
                end
            end
        end
    end
end

function check_for_pirates(x::EXPR)
    if CSTParser.defines_function(x) && hasbinding(x) && overwrites_imported_function(bindingof(x))
        sig = CSTParser.rem_where_decl(CSTParser.get_sig(x))
        if typof(sig) == CSTParser.Call
            for i = 2:length(sig)
                if hasbinding(sig[i]) && bindingof(sig[i]).type isa Binding
                    return
                elseif refers_to_nonimported_type(sig[i])
                    return
                end
            end
            seterror!(x, TypePiracy)
        end
    end
end

function refers_to_nonimported_type(arg::EXPR)
    if hasref(arg) && refof(arg) isa Binding
        return true
    elseif typof(arg) === CSTParser.UnaryOpCall && length(arg) == 2 && kindof(arg[1]) === CSTParser.Tokens.DECLARATION
        return refers_to_nonimported_type(arg[2])
    elseif _binary_assert(arg, CSTParser.Tokens.DECLARATION)
        return refers_to_nonimported_type(arg[3])
    elseif typof(arg) === CSTParser.Curly
        for i = 1:length(arg)
            if refers_to_nonimported_type(arg[i])
                return true
            end
        end
        return false
    end
    return false
end

overwrites_imported_function(b, visited_bindings = Binding[]) = false
function overwrites_imported_function(b::Binding, visited_bindings = Binding[])
    if b in visited_bindings
        return false
    else
        push!(visited_bindings, b)
    end

    if b.prev isa Binding
        if b.prev.val isa EXPR
            # overwrites a within source bindig so lets check that
            return overwrites_imported_function(b.prev, visited_bindings)
        elseif (b.prev.val isa SymbolServer.FunctionStore || b.prev.val isa SymbolServer.DataTypeStore) && parentof(b.prev.name) isa EXPR && typof(parentof(b.prev.name)) === CSTParser.Import
            # explicitly imported, e.g. import ModuleName: somefunction
            return true
        end
    elseif b.prev isa SymbolServer.FunctionStore &&
        parentof(b.name) isa EXPR && typof(parentof(b.name)) === CSTParser.Quotenode && is_getfield(parentof(parentof(b.name)))
        fullname = parentof(parentof(b.name))
        # overwrites imported function by declaring full name, e.g. ModuleName.FunctionName
        if CSTParser.isidentifier(fullname[1]) && refof(fullname[1]) isa SymbolServer.ModuleStore
            return true
        elseif is_getfield(fullname[1]) && typof(fullname[1][3]) === CSTParser.Quotenode && refof(fullname[1][3][1]) isa SymbolServer.ModuleStore
            return true
        end
    end
    return false
end
