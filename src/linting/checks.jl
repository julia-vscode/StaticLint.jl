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
    if typof(x) in (CSTParser.Abstract, CSTParser.Primitive, CSTParser.Struct, CSTParser.Mutable)
        return CoreTypes.DataType
    elseif typof(x) in (CSTParser.ModuleH, CSTParser.BareModule)
        return CoreTypes.Module
    elseif CSTParser.defines_function(x)
        return CoreTypes.Function
    end
end

# Call
function struct_nargs(x::EXPR)
    # struct defs wrapped in macros are likely to have some arbirtary additional constructors, so lets allow anything
    parentof(x) isa EXPR && typof(parentof(x)) === CSTParser.MacroCall && return 0, typemax(Int), String[], true 
    minargs, maxargs, kws, kwsplat = 0, 0, String[], false
    args = typof(x) === CSTParser.Mutable ? x.args[4] : x.args[3]
    args.args === nothing && return 0, typemax(Int), kws, kwsplat
    inner_constructor = findfirst(a->CSTParser.defines_function(a), args.args)
    if inner_constructor !== nothing
        return func_nargs(args.args[inner_constructor])
    else
        minargs = maxargs = length(args.args)
    end
    return minargs, maxargs, kws, kwsplat
end

function func_nargs(x::EXPR)
    minargs, maxargs, kws, kwsplat = 0, 0, String[], false
    sig = CSTParser.rem_where_decl(CSTParser.get_sig(x))
    if sig.args isa Vector{EXPR}
        for i = 2:length(sig.args)
            arg = sig.args[i]
            if typof(arg) === CSTParser.MacroCall && arg.args isa Vector{EXPR} && length(arg.args) > 1 &&
                _expr_assert(arg.args[1], MacroName, 2) && valof(arg.args[1].args[2]) == "nospecialize"
                if length(arg.args) == 2
                    arg = arg.args[2]
                end
            end
            if typof(arg) === CSTParser.PUNCTUATION
                # skip
            elseif typof(arg) === CSTParser.Parameters
                for j = 1:length(arg)
                    arg1 = arg.args[j]
                    if typof(arg1) === CSTParser.Kw
                        push!(kws, CSTParser.str_value(CSTParser.get_arg_name(arg1.args[1])))
                    elseif typof(arg1) === CSTParser.UnaryOpCall && kindof(arg1.args[2]) === CSTParser.Tokens.DDDOT
                        kwsplat = true
                    end
                end
            elseif typof(arg) === CSTParser.Kw
                if typof(arg.args[1]) === UnaryOpCall && kindof(arg.args[1].args[2]) === CSTParser.Tokens.DDDOT
                    maxargs = typemax(Int)
                else
                    maxargs !== typemax(Int) && (maxargs += 1)
                end
            elseif (typof(arg) === UnaryOpCall && kindof(arg.args[2]) === CSTParser.Tokens.DDDOT) ||
                (_binary_assert(arg, CSTParser.Tokens.DECLARATION) &&
                ((typof(arg.args[3]) === CSTParser.IDENTIFIER && valof(arg.args[3]) == "Vararg") ||
                (typof(arg.args[3]) === CSTParser.Curly && typof(arg.args[3].args[1]) === CSTParser.IDENTIFIER && valof(arg.args[3].args[1]) == "Vararg")))
                maxargs = typemax(Int)
            else
                minargs += 1
                maxargs !== typemax(Int) && (maxargs += 1)
            end
        end
    end
    return minargs, maxargs, kws, kwsplat
end

function func_nargs(m::SymbolServer.MethodStore)
    minargs, maxargs, kws, kwsplat = 0, 0, String[], false
    for a in m.args
        if last(a) == ".KW"
            if endswith(first(a), "...")
                kwsplat = true
            else
                push!(kws, first(a))
            end
        elseif startswith(last(a), "Vararg") || endswith(first(a), "...") || endswith(last(a), "...")
            maxargs = typemax(Int)
        else
            minargs += 1
            maxargs !== typemax(Int) && (maxargs += 1)
        end
    end
    return minargs, maxargs, kws, kwsplat
end

function call_nargs(x::EXPR)
    minargs, maxargs, kws = 0, 0, String[]
    if x.args isa Vector{EXPR}
        for i = 2:length(x.args)
            arg = x.args[i]
            if typof(arg) === CSTParser.PUNCTUATION
                # skip
            elseif typof(x.args[i]) === CSTParser.Parameters
                for j = 1:length(x.args[i])
                    arg = x.args[i].args[j]
                    if typof(arg) === CSTParser.Kw
                        push!(kws, CSTParser.str_value(CSTParser.get_arg_name(arg.args[1])))
                    end
                end
            elseif typof(arg) === CSTParser.Kw
                push!(kws, CSTParser.str_value(CSTParser.get_arg_name(arg.args[1])))
            elseif typof(arg) === CSTParser.UnaryOpCall && kindof(arg.args[2]) === CSTParser.Tokens.DDDOT
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

function compare_f_call(m_counts::Tuple{Int,Int,Array{String},Bool}, call_counts::Tuple{Int,Int,Array{String}})
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
        x.args === nothing || isempty(x.args) && return
        if typof(first(x.args)) === IDENTIFIER && hasref(first(x.args))
            func_ref = refof(first(x.args))
        elseif _binary_assert(first(x), CSTParser.Tokens.DOT) && typof(first(x).args[3]) === CSTParser.Quotenode && first(x).args[3].args !== nothing && !isempty(first(x).args[3].args) && typof(first(x).args[3].args[1]) === IDENTIFIER && hasref(first(x).args[3].args[1])
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
            seterror!(x, IncorrectCallArgs)
        elseif func_ref isa Binding && (func_ref.type === CoreTypes.Function || func_ref.type === CoreTypes.DataType)
            call_counts = call_nargs(x)
            b = func_ref
            while b.next isa Binding && b.next.type == CoreTypes.Function
                b = b.next
            end
            while true
                if !(b isa Binding) # Needs to be cleaned up
                    if b isa SymbolServer.FunctionStore || b isa SymbolServer.DataTypeStore
                        for m in b.methods
                            m_counts = func_nargs(m)
                            if compare_f_call(m_counts, call_counts)
                                return
                            end
                        end
                        break
                    else
                        return
                    end
                elseif b.type == CoreTypes.Function
                    m_counts = func_nargs(b.val)
                elseif b.type == CoreTypes.DataType && CSTParser.defines_struct(b.val)
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
            seterror!(x, IncorrectCallArgs)
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
        elseif _binary_assert(cond, CSTParser.Tokens.EQ)
            seterror!(cond, EqInIfConditional)
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
        elseif typof(last(x.args)) === CSTParser.LITERAL
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
        if missing && CSTParser.isidentifier(x) && !hasref(x) && 
            !(valof(x) == "var" && parentof(x) isa EXPR && typof(parentof(x)) === CSTParser.NONSTDIDENTIFIER) &&
            !((valof(x) == "stdcall" || valof(x) == "cdecl" || valof(x) == "fastcall" || valof(x) == "thiscall" || valof(x) == "llvmcall") && is_in_fexpr(x, x->typof(x) === CSTParser.Call && isidentifier(x.args[1]) && valof(x.args[1]) == "ccall"))
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

function check_typeparams(x::EXPR)
    if typof(x) === CSTParser.WhereOpCall
        for i = 3:length(x.args)
            if hasbinding(x.args[i])
                if !(bindingof(x.args[i]).refs isa Vector) 
                    seterror!(x.args[i], UnusedTypeParameter)
                elseif length(bindingof(x.args[i]).refs) == 1
                    # there should (will?) always be at least one reference in the where declaration
                    seterror!(x.args[i], UnusedTypeParameter)
                end
            end
        end
    end
end

function check_for_pirates(x::EXPR)
    if CSTParser.defines_function(x) && hasbinding(x) && overwrites_imported_function(bindingof(x))
        sig = CSTParser.rem_where_decl(CSTParser.get_sig(x))
        if typof(sig) == CSTParser.Call
            for i = 2:length(sig.args)
                if hasbinding(sig.args[i]) && bindingof(sig.args[i]).type isa Binding
                    return
                elseif refers_to_nonimported_type(sig.args[i])
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
    elseif typof(arg) === CSTParser.UnaryOpCall && length(arg.args) == 2 && kindof(arg.args[1]) === CSTParser.Tokens.DECLARATION
        return refers_to_nonimported_type(arg.args[2])
    elseif _binary_assert(arg, CSTParser.Tokens.DECLARATION)
        return refers_to_nonimported_type(arg.args[3])
    elseif typof(arg) === CSTParser.Curly
        for i = 1:length(arg.args)
            if refers_to_nonimported_type(arg.args[i])
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
        parentof(b.name) isa EXPR && typof(parentof(b.name)) === CSTParser.Quotenode && 
        parentof(parentof(b.name)) isa EXPR && typof(parentof(parentof(b.name))) === CSTParser.BinaryOpCall && kindof(parentof(parentof(b.name))[2]) === CSTParser.Tokens.DOT
        fullname = parentof(parentof(b.name))
        # overwrites imported function by declaring full name, e.g. ModuleName.FunctionName
        if CSTParser.isidentifier(fullname.args[1]) && refof(fullname.args[1]) isa SymbolServer.ModuleStore
            return true
        elseif typof(fullname.args[1]) === CSTParser.BinaryOpCall && kindof(fullname.args[1].args[2]) == CSTParser.Tokens.DOT && typof(fullname.args[1].args[3]) === CSTParser.Quotenode && refof(fullname.args[1].args[3].args[1]) isa SymbolServer.ModuleStore
            return true
        end
    end
    return false
end
