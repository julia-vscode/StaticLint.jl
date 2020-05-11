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
TypePiracy,
UnusedFunctionArgument,
CannotDeclareConst,
InvalidRedefofConst,
NotEqDef)


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
    TypePiracy => "An imported function has been extended without using module defined typed arguments.",
    UnusedFunctionArgument => "An argument is included in a function signature but not used within its body.",
    CannotDeclareConst => "Cannot declare constant; it already has a value.",
    InvalidRedefofConst => "Invalid redefinition of constant.",
    NotEqDef => "`!=` is defined as `const != = !(==)` and should not be overloaded. Overload `==` instead.")

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
        elseif CSTParser.defines_module(x)
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
    parentof(x) isa EXPR && is_macro_call(parentof(x)) && return 0, typemax(Int), Symbol[], true 
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
        if is_macro_call(arg) && length(arg) > 1 &&
            is_macroname(arg[1]) && valof(arg[1][2]) == "nospecialize"
            if length(arg) == 2
                arg = arg[2]
            end
        end
        if ispunctuation(arg)
            # skip
        elseif typof(arg) === CSTParser.Parameters
            for j = 1:length(arg)
                arg1 = arg[j]
                if is_kwarg(arg1)
                    push!(kws, Symbol(CSTParser.str_value(CSTParser.get_arg_name(arg1[1]))))
                elseif is_binary_call(arg1) && kindof(arg1[2]) === CSTParser.Tokens.DDDOT
                    kwsplat = true
                end
            end
        elseif is_kwarg(arg)
            if is_unary_call(arg[1]) && kindof(arg[1][2]) === CSTParser.Tokens.DDDOT
                maxargs = typemax(Int)
            else
                maxargs !== typemax(Int) && (maxargs += 1)
            end
        elseif (is_unary_call(arg) && kindof(arg[2]) === CSTParser.Tokens.DDDOT) ||
            (is_declaration(arg) &&
            ((isidentifier(arg[3]) && valofid(arg[3]) == "Vararg") ||
            (typof(arg[3]) === CSTParser.Curly && isidentifier(arg[3][1]) && valofid(arg[3][1]) == "Vararg")))
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
            if ispunctuation(arg)
                # skip
            elseif typof(x[i]) === CSTParser.Parameters
                for j = 1:length(x[i])
                    arg = x[i][j]
                    if is_kwarg(arg)
                        push!(kws, Symbol(CSTParser.str_value(CSTParser.get_arg_name(arg[1]))))
                    end
                end
            elseif is_kwarg(arg)
                push!(kws, Symbol(CSTParser.str_value(CSTParser.get_arg_name(arg[1]))))
            elseif is_unary_call(arg) && kindof(arg[2]) === CSTParser.Tokens.DDDOT
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
    if is_call(x)
        parentof(x) isa EXPR && typof(parentof(x)) === CSTParser.Do && return # TODO: add number of args specified in do block.
        length(x) == 0 && return
        if isidentifier(first(x)) && hasref(first(x))
            func_ref = refof(first(x))
        elseif is_binary_call(x[1], CSTParser.Tokens.DOT) && typof(x[1]) === CSTParser.Quotenode && length(x[1][3]) > 0 && isidentifier(x[1][3][1]) && hasref(first(x)[3][1])
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
            tls === nothing && return
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
                        tls === nothing && return 
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
                    tls === nothing && return 
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
        if length(x) > 1 && is_binary_call(x[2]) && refof(x[2]) === nothing
            rng = x[2][3]
            if typof(rng) === CSTParser.LITERAL && kindof(rng) == CSTParser.Tokens.FLOAT || kindof(rng) == CSTParser.Tokens.INTEGER
                seterror!(x[2], IncorrectIterSpec)
            elseif is_call(rng) && refof(rng[1]) === getsymbolserver(server)[:Base][:length]
                seterror!(x[2], IncorrectIterSpec)
            end
        end
    elseif typof(x) === CSTParser.Generator
        for i = 3:length(x)
            if is_binary_call(x[i])&& refof(x[i]) === nothing
                rng = x[i][3]
                if typof(rng) === CSTParser.LITERAL && kindof(rng) == CSTParser.Tokens.FLOAT || kindof(rng) == CSTParser.Tokens.INTEGER
                    seterror!(x[i], IncorrectIterSpec)
                elseif is_call(rng) && valof(rng[1]) == "length" && refof(rng[1]) === getsymbolserver(server)[:Base][:length]
                    seterror!(x[i], IncorrectIterSpec)
                end
            end
        end
    end
end

function check_nothing_equality(x::EXPR, server)
    if is_binary_call(x)
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
        cond = iskw(first(x)) ? x[2] : x[1]
        if typof(cond) === CSTParser.LITERAL && (kindof(cond) === CSTParser.Tokens.TRUE || kindof(cond) === CSTParser.Tokens.FALSE)
            seterror!(cond, ConstIfCondition)
        elseif is_binary_call(cond, CSTParser.Tokens.EQ)
            seterror!(cond, EqInIfConditional)
        end
    end
end

function check_lazy(x::EXPR)
    if is_binary_call(x)
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

is_never_datatype(b, server) = false
is_never_datatype(b::SymbolServer.DataTypeStore, server) = false
function is_never_datatype(b::SymbolServer.FunctionStore, server)
    !(SymbolServer._lookup(b.extends, getsymbolserver(server)) isa SymbolServer.DataTypeStore)
end
function is_never_datatype(b::Binding, server)
    if b.val isa Binding
        return is_never_datatype(b.val, server)
    elseif b.type == CoreTypes.DataType
        return false
    elseif b.type == CoreTypes.Function && b.prev !== nothing
        return is_never_datatype(b.prev, server)
    elseif b.type !== nothing
        return true
    end
    return false
end

function check_datatype_decl(x::EXPR, server)
    # Only call in function signatures?
    if is_declaration(x) && parentof(x) isa EXPR && is_call(parentof(x))
        if (dt = refof_maybe_getfield(last(x))) !== nothing
            if is_never_datatype(dt, server)
                seterror!(x, InvalidTypeDeclaration)
            end
        elseif typof(last(x)) === CSTParser.LITERAL
            seterror!(x, InvalidTypeDeclaration)
        end
    end    
end

function check_modulename(x::EXPR)
    if CSTParser.defines_module(x) && # x is a module
        scopeof(x) isa Scope && parentof(scopeof(x)) isa Scope && # it has a scope and a parent scope
        CSTParser.defines_module(parentof(scopeof(x)).expr) && # the parent scope is a module
        valof(CSTParser.get_name(x)) == valof(CSTParser.get_name(parentof(scopeof(x)).expr)) # their names match
        seterror!(CSTParser.get_name(x), InvalidModuleName)
    end
end

# Check whether function arguments are unused
function check_farg_unused(x::EXPR)
    if CSTParser.defines_function(x)
        sig = CSTParser.rem_where_decl(CSTParser.get_sig(x))
        if (typof(x) === CSTParser.FunctionDef && length(x) == 4 && x[3] isa EXPR && length(x[3]) == 1 && CSTParser.isliteral(x[3][1])) ||
            (typof(x[3]) === CSTParser.Block && length(x[3]) == 1 && CSTParser.isliteral(x[3][1]))
            return # Allow functions that return constants
        end
        if is_call(sig)
            for i = 2:length(sig)
                if hasbinding(sig[i])
                    arg = sig[i]
                elseif is_kwarg(sig[i]) && hasbinding(sig[i][1])
                    arg = sig[i][1]
                else
                    continue
                end
                b = bindingof(arg)
                if (isempty(b.refs) || (length(b.refs) == 1 && first(b.refs) == b.name)) &&
                    b.next === nothing
                    seterror!(arg, UnusedFunctionArgument)
                end
            end
        end
    end
end

const default_options = (true, true, true, true, true, true, true, true, true, true)

struct LintOptions
    call::Bool
    iter::Bool
    nothingcomp::Bool
    constif::Bool
    lazy::Bool
    datadecl::Bool
    typeparam::Bool
    modname::Bool
    pirates::Bool
    useoffuncargs::Bool
end
LintOptions() = LintOptions(default_options...)
LintOptions(::Colon) = LintOptions(fill(true, length(default_options))...)

LintOptions(options::Vararg{Union{Bool,Nothing},length(default_options)}) =
    LintOptions(something.(options, default_options)...)

function check_all(x::EXPR, opts::LintOptions, server)
    # Do checks
    opts.call && check_call(x, server)
    opts.iter && check_loop_iter(x, server)
    opts.nothingcomp && check_nothing_equality(x, server)
    opts.constif && check_if_conds(x)
    opts.lazy && check_lazy(x)
    opts.datadecl && check_datatype_decl(x, server)
    opts.typeparam && check_typeparams(x)
    opts.modname && check_modulename(x)
    opts.pirates && check_for_pirates(x)
    opts.useoffuncargs && check_farg_unused(x)
    check_const_decl(x)
    check_const_redef(x)
    for i in 1:length(x)
        check_all(x[i], opts, server)
    end
end


"""
collect_hints(x::EXPR, server, missingrefs = :all, isquoted = false, errs = Tuple{Int,EXPR}[], pos = 0)

Collect hints and errors from an expression. `missingrefs` = (:none, :id, :all) determines whether unresolved
identifiers are marked, the :all option will mark identifiers used in getfield calls."
"""
function collect_hints(x::EXPR, server, missingrefs = :all, isquoted = false, errs = Tuple{Int,EXPR}[], pos = 0)
    if quoted(x)
        isquoted = true
    elseif isquoted && unquoted(x)
        isquoted = false
    end
    if typof(x) === CSTParser.ErrorToken 
        # collect parse errors
        push!(errs, (pos, x))
    elseif !isquoted
        if missingrefs != :none && CSTParser.isidentifier(x) && !hasref(x) && 
            !(valof(x) == "var" && parentof(x) isa EXPR && isnonstdid(parentof(x))) &&
            !((valof(x) == "stdcall" || valof(x) == "cdecl" || valof(x) == "fastcall" || valof(x) == "thiscall" || valof(x) == "llvmcall") && is_in_fexpr(x, x->is_call(x) && isidentifier(x[1]) && valof(x[1]) == "ccall"))
            push!(errs, (pos, x))
        elseif haserror(x) && errorof(x) isa StaticLint.LintCodes
            # collect lint hints
            push!(errs, (pos, x))
        end
    elseif isquoted && missingrefs == :all && should_mark_missing_getfield_ref(x, server)
            push!(errs, (pos, x))
    end

    for i in 1:length(x)
        collect_hints(x[i], server, missingrefs, isquoted, errs, pos)
        pos += x[i].fullspan
    end
    
    errs
end

function refof_maybe_getfield(x::EXPR)
    if isidentifier(x) 
        return refof(x)
    elseif is_getfield_w_quotenode(x)
        return refof(x[3][1])
    end
end

function should_mark_missing_getfield_ref(x, server)
    if CSTParser.isidentifier(x) && !hasref(x) && # x has no ref
    parentof(x) isa EXPR && typof(parentof(x)) === CSTParser.Quotenode && parentof(parentof(x)) isa EXPR && 
        is_getfield(parentof(parentof(x)))  # x is the rhs of a getproperty
        lhsref = refof_maybe_getfield(parentof(parentof(x))[1])
        if lhsref isa SymbolServer.ModuleStore || (lhsref isa Binding && lhsref.val isa SymbolServer.ModuleStore) 
            # a module, we should know this.
            return true
        elseif lhsref isa Binding
            if lhsref.val isa Binding
                lhsref = lhsref.val
            end
            lhsref = get_root_method(lhsref, nothing)
            if lhsref.type isa SymbolServer.DataTypeStore && !(isempty(lhsref.type.fieldnames) || isunionfaketype(lhsref.type.name) || has_getproperty_method(lhsref.type, server))
                return true
            elseif lhsref.type isa Binding && lhsref.type.val isa EXPR && CSTParser.defines_struct(lhsref.type.val) && !has_getproperty_method(lhsref.type)
                return true
            end
        end
    end
    return false
end

unwrap_fakeunionall(x) = x isa SymbolServer.FakeUnionAll ? unwrap_fakeunionall(x.body) : x
function has_getproperty_method(b::SymbolServer.DataTypeStore, server)
    getprop_vr = SymbolServer.VarRef(SymbolServer.VarRef(nothing, :Base), :getproperty)
    if haskey(getsymbolextendeds(server), getprop_vr)
        for ext in getsymbolextendeds(server)[getprop_vr]
            for m in SymbolServer._lookup(ext, getsymbolserver(server))[:getproperty].methods
                t = unwrap_fakeunionall(m.sig[1][2])
                t.name == b.name.name && return true
            end
        end
    else
        for m in getsymbolserver(server)[:Base][:getproperty].methods
            t = unwrap_fakeunionall(m.sig[1][2])
            t.name == b.name.name && return true
        end
    end
    return false
end

function has_getproperty_method(b::Binding)
    if b.val isa Binding
        return has_getproperty_method(b.val)
    elseif b.val isa SymbolServer.DataTypeStore
        return has_getproperty_method(b.val)
    elseif  b isa Binding && b.type === CoreTypes.DataType
        while b !== nothing
            for ref in b.refs
                if is_type_of_call_to_getproperty(ref)
                    return true
                end
            end
            b = b.next isa Binding && b.next.type === CoreTypes.Function ? b.next : nothing
        end
        
    end
    return false
end

function is_type_of_call_to_getproperty(x::EXPR)
    function is_call_to_getproperty(x::EXPR) 
        if is_call(x)
            func_name = x[1]
            return (isidentifier(func_name) && valof(func_name) == "getproperty") || # getproperty()
            (is_getfield_w_quotenode(func_name) && isidentifier(func_name[3][1]) && valof(func_name[3][1]) == "getproperty") # Base.getproperty()
        end
        return false
    end

    return parentof(x) isa EXPR && parentof(parentof(x)) isa EXPR && 
        ((is_declaration(parentof(x)) && x === parentof(x)[3] && is_call_to_getproperty(parentof(parentof(x)))) || 
        (typof(parentof(x)) === CSTParser.Curly && x === parentof(x)[1] && is_declaration(parentof(parentof(x))) &&  parentof(parentof(parentof(x))) isa EXPR && is_call_to_getproperty(parentof(parentof(parentof(x))))))
end

isunionfaketype(t::SymbolServer.FakeTypeName) = t.name.name === :Union && t.name.parent isa SymbolServer.VarRef && t.name.parent.name === :Core

function check_typeparams(x::EXPR)
    if is_where(x)
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
    if CSTParser.defines_function(x)
        sig = CSTParser.rem_where_decl(CSTParser.get_sig(x))
        if fname_is_noteq(CSTParser.get_name(sig))
            seterror!(x, NotEqDef)
        elseif is_call(sig) && hasbinding(x) && overwrites_imported_function(bindingof(x))
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

function fname_is_noteq(x)
    if x isa EXPR
        if isoperator(x) && kindof(x) === CSTParser.Tokens.NOT_EQ
            return true
        elseif is_getfield_w_quotenode(x) && length(x[3]) == 2 && CSTParser.is_colon(x[3][1])

            return fname_is_noteq(x[3][2])
        end
    end
    return false
end

function refers_to_nonimported_type(arg::EXPR)
    if hasref(arg) && refof(arg) isa Binding
        return true
    elseif is_unary_call(arg) && (kindof(arg[1]) === CSTParser.Tokens.DECLARATION || kindof(arg[1]) === CSTParser.Tokens.ISSUBTYPE)
        return refers_to_nonimported_type(arg[2])
    elseif is_declaration(arg)
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

function check_const_decl(x::EXPR)
    if CSTParser.defines_datatype(x) && hasbinding(x) && bindingof(x).prev !== nothing
        seterror!(x, CannotDeclareConst)
    end
end

function check_const_redef(x::EXPR)
    if hasbinding(x) && bindingof(x) isa Binding && bindingof(x).prev isa Binding && bindingof(x).prev.type === CoreTypes.DataType && bindingof(x).type !== CoreTypes.Function
        seterror!(x, InvalidRedefofConst)
    end
end
