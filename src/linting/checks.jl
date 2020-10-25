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
NotEqDef,
KwDefaultMismatch,
InappropriateUseOfLiteral,
ShouldBeInALoop)



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
    NotEqDef => "`!=` is defined as `const != = !(==)` and should not be overloaded. Overload `==` instead.",
    KwDefaultMismatch => "The default value provided does not match the specified argument type.",
    InappropriateUseOfLiteral => "You really shouldn't be using a literal value here.",
    ShouldBeInALoop => "`break` or `continue` used outside loop."
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
    check_kw_default(x, server)
    check_use_of_literal(x)
    check_break_continue(x)

    if x.args !== nothing
        for i in 1:length(x.args)
            check_all(x.args[i], opts, server)
        end
    end
end


function _typeof(x, state)
    if x isa EXPR
        if headof(x) in (:abstract, :primitive, :struct)
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
    parentof(x) isa EXPR && CSTParser.ismacrocall(parentof(x)) && return 0, typemax(Int), Symbol[], true
    minargs, maxargs, kws, kwsplat = 0, 0, Symbol[], false
    args = x.args[3]
    length(args.args) == 0 && return 0, typemax(Int), kws, kwsplat
    inner_constructor = findfirst(a->CSTParser.defines_function(a), args.args)
    if inner_constructor !== nothing
        return func_nargs(args.args[inner_constructor])
    else
        minargs = maxargs = length(args.args)
    end
    return minargs, maxargs, kws, kwsplat
end

function func_nargs(x::EXPR)
    minargs, maxargs, kws, kwsplat = 0, 0, Symbol[], false
    sig = rem_wheres_decls(CSTParser.get_sig(x))
    if sig.args !== nothing
        for i = 2:length(sig.args)
            # arg = sig.args[i]
            # if CSTParser.ismacrocall(arg) && length(arg.args) == 3 && CSTParser.ismacroname(arg.args[1]) && isidentifier(arg.args[1]) && valofid(arg.args[1]) == "@nospecialize"
            #     arg = arg.args[3]
            # end
            
            arg = unwrap_nospecialize(sig.args[i])
            if isparameters(arg)
                for j = 1:length(arg.args)
                    arg1 = arg.args[j]
                    if iskwarg(arg1)
                        push!(kws, Symbol(CSTParser.str_value(CSTParser.get_arg_name(arg1.args[1]))))
                    elseif issplat(arg1)
                        kwsplat = true
                    end
                end
            elseif iskwarg(arg)
                if issplat(arg.args[1])
                    maxargs = typemax(Int)
                else
                    maxargs !== typemax(Int) && (maxargs += 1)
                end
            elseif issplat(arg) ||
                (isdeclaration(arg) &&
                ((isidentifier(arg.args[2]) && valofid(arg.args[2]) == "Vararg") ||
                (iscurly(arg.args[2]) && isidentifier(arg.args[2].args[1]) && valofid(arg.args[2].args[1]) == "Vararg")))
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
    if length(x.args) > 0
        for i = 2:length(x.args)
            arg = x.args[i]
            if isparameters(arg)
                for j = 1:length(arg.args)
                    arg1 = arg.args[j]
                    if iskwarg(arg1)
                        push!(kws, Symbol(CSTParser.str_value(CSTParser.get_arg_name(arg1.args[1]))))
                    end
                end
            elseif iskwarg(arg)
                push!(kws, Symbol(CSTParser.str_value(CSTParser.get_arg_name(arg.args[1]))))
            elseif issplat(arg)
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

function is_something_with_methods(x::Binding)
    (x.type == CoreTypes.Function && x.val isa EXPR) ||
    (x.type == CoreTypes.DataType && x.val isa EXPR && CSTParser.defines_struct(x.val)) ||
    (x.val isa SymbolServer.FunctionStore || x.val isa SymbolServer.DataTypeStore)
end
is_something_with_methods(x::T) where T <: Union{SymbolServer.FunctionStore,SymbolServer.DataTypeStore} = true
is_something_with_methods(x) = false

function check_call(x, server)
    if iscall(x)
        parentof(x) isa EXPR && headof(parentof(x)) === :do && return # TODO: add number of args specified in do block.
        length(x.args) == 0 && return
        # find the function we're dealing with
        if isidentifier(first(x.args)) && hasref(first(x.args))
            func_ref = refof(first(x.args))
        elseif is_getfield_w_quotenode(x.args[1]) && (rhs = rhs_of_getfield(x.args[1])) !== nothing && hasref(rhs)
            func_ref = refof(rhs)
        else
            return
        end

        if func_ref isa Binding && (func_ref.type === CoreTypes.Function || func_ref.type === CoreTypes.DataType)
            func_ref = last_method(func_ref)
        elseif func_ref isa SymbolServer.FunctionStore || func_ref isa SymbolServer.DataTypeStore
            # intentionally empty
        else
            return
        end
        call_counts = call_nargs(x)
        tls = retrieve_toplevel_scope(x)
        tls === nothing && return # General check, this means something serious has gone wrong.
        !sig_match_any(func_ref, x, call_counts, tls, server) && seterror!(x, IncorrectCallArgs)

    end
end

function sig_match_any(func_ref, x, call_counts, tls, server, visited = [])
    if func_ref in visited
        return true
    else
        push!(visited, func_ref)
    end
    if func_ref isa Binding && (func_ref.val isa SymbolServer.FunctionStore || func_ref.val isa SymbolServer.DataTypeStore)
        func_ref = func_ref.val
    end
    if func_ref isa SymbolServer.FunctionStore || func_ref isa SymbolServer.DataTypeStore
        return iterate_over_ss_methods(func_ref, tls, server, m->compare_f_call(func_nargs(m), call_counts))
    elseif func_ref isa Binding
        if func_ref.type == CoreTypes.Function && func_ref.val isa EXPR
            m_counts = func_nargs(func_ref.val)
        elseif func_ref.type == CoreTypes.DataType && func_ref.val isa EXPR && CSTParser.defines_struct(func_ref.val)
            m_counts = struct_nargs(func_ref.val)
        else
            # We shouldn't get here
            return true
        end
        if compare_f_call(m_counts, call_counts) || (CSTParser.rem_where_decl(CSTParser.get_sig(func_ref.val)) == x)
            return true
        end
        if is_something_with_methods(func_ref.prev)
            return sig_match_any(func_ref.prev, x, call_counts, tls, server, visited)
        elseif func_ref.prev isa Binding && func_ref.prev.type === nothing && func_ref.prev.val isa EXPR && isidentifier(func_ref.prev.val) &&
            isdocumented(func_ref.prev.val) # && is_something_with_methods(func_ref.prev.prev)
            # Skip over documented symbols
            return sig_match_any(func_ref.prev.prev, x, call_counts, tls, server, visited)
        end
    end
    return false
end

isdocumented(x::EXPR) = parentof(x) isa EXPR && CSTParser.ismacrocall(parentof(x)) && headof(parentof(x).args[1]) === :globalrefdoc

function check_loop_iter(x::EXPR, server)
    if headof(x) === :for
        if length(x.args) > 0 && CSTParser.is_range(x.args[1])
            rng = rhs_of_iterator(x.args[1])
            if headof(rng) === :FLOAT || headof(rng) === :INTEGER || (iscall(rng) && refof(rng.args[1]) === getsymbolserver(server)[:Base][:length])
                seterror!(x.args[1], IncorrectIterSpec)
            end
        end
    elseif headof(x) === :generator
        for i = 2:length(x.args)
            if CSTParser.is_range(x.args[i])
                rng = rhs_of_iterator(x.args[i])
                if headof(rng) === :FLOAT || headof(rng) === :INTEGER || (iscall(rng) && refof(rng.args[1]) === getsymbolserver(server)[:Base][:length])
                    seterror!(x.args[i], IncorrectIterSpec)
                end
            end
        end
    end
end

function check_nothing_equality(x::EXPR, server)
    if isbinarycall(x)
        if valof(x.args[1]) == "==" && valof(x.args[3]) == "nothing" && refof(x.args[3]) === getsymbolserver(server)[:Core][:nothing]
            seterror!(x.args[1], NothingEquality)
        elseif valof(x.args[1]) == "!=" && valof(x.args[3]) == "nothing" && refof(x.args[3]) === getsymbolserver(server)[:Core][:nothing]
            seterror!(x.args[1], NothingNotEq)
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
    if !CSTParser.defines_module(s.expr) && parentof(s) isa Scope && parentof(s) != s
        return _get_global_scope(parentof(s))
    else
        return s
    end
end

function check_if_conds(x::EXPR)
    if headof(x) === :if
        cond = x.args[1]
        if headof(cond) === :TRUE || headof(cond) === :FALSE
            seterror!(cond, ConstIfCondition)
        elseif isassignment(cond)
            seterror!(cond, EqInIfConditional)
        end
    end
end

function check_lazy(x::EXPR)
    if isbinarysyntax(x)
        if valof(headof(x)) == "||"
            if headof(x.args[1]) === :TRUE || headof(x.args[1]) === :FALSE
                seterror!(x, PointlessOR)
            end
        elseif valof(headof(x)) == "&&"
            if headof(x.args[1]) === :TRUE || headof(x.args[1]) === :FALSE || headof(x.args[2]) === :TRUE || headof(x.args[2]) === :FALSE
                seterror!(x, PointlessAND)
            end
        end
    end
end

is_never_datatype(b, server, visited = nothing) = false
is_never_datatype(b::SymbolServer.DataTypeStore, server, visited = nothing) = false
function is_never_datatype(b::SymbolServer.FunctionStore, server, visited = nothing)
    !(SymbolServer._lookup(b.extends, getsymbolserver(server)) isa SymbolServer.DataTypeStore)
end
function is_never_datatype(b::Binding, server, visited = Binding[])
    if b in visited
        return false
    else
        push!(visited, b)
    end
    if b.val isa Binding
        return is_never_datatype(b.val, server, visited)
    elseif b.val isa SymbolServer.FunctionStore
        return is_never_datatype(b.val, server)
    elseif b.type == CoreTypes.DataType
        return false
    elseif b.type == CoreTypes.Function && b.prev !== nothing
        return is_never_datatype(b.prev, server, visited)
    elseif b.type !== nothing
        return true
    end
    return false
end

function check_datatype_decl(x::EXPR, server)
    # Only call in function signatures?
    if isdeclaration(x) && parentof(x) isa EXPR && iscall(parentof(x))
        if (dt = refof_maybe_getfield(last(x.args))) !== nothing
            if is_never_datatype(dt, server)
                seterror!(x, InvalidTypeDeclaration)
            end
        elseif CSTParser.isliteral(last(x.args))
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
        if (headof(x) === :function && length(x.args) == 2 && x.args[2] isa EXPR && length(x.args[2].args) == 1 && CSTParser.isliteral(x.args[2].args[1])) ||
            (length(x.args) > 1 && headof(x.args[2]) === :block && length(x.args[2].args) == 1 && CSTParser.isliteral(x.args[2].args[1]))
            return # Allow functions that return constants
        end
        if iscall(sig)
            for i = 2:length(sig.args)
                if hasbinding(sig.args[i])
                    arg = sig.args[i]
                elseif iskwarg(sig.args[i]) && hasbinding(sig.args[i].args[1])
                    arg = sig.args[i].args[1]
                elseif is_nospecialize_call(sig.args[i]) && hasbinding(unwrap_nospecialize(sig.args[i]))
                    arg = unwrap_nospecialize(sig.args[i])
                else
                    return
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

function unwrap_nospecialize(x)
    is_nospecialize_call(x) || return x
    x.args[3]
end

function is_nospecialize_call(x)
    CSTParser.ismacrocall(x) && 
    CSTParser.ismacroname(x.args[1]) && 
    is_nospecialize(x.args[1])
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
    if headof(x) === :errortoken
        # collect parse errors
        push!(errs, (pos, x))
    elseif !isquoted
        if missingrefs != :none && isidentifier(x) && !hasref(x) &&
            !(valof(x) == "var" && parentof(x) isa EXPR && isnonstdid(parentof(x))) &&
            !((valof(x) == "stdcall" || valof(x) == "cdecl" || valof(x) == "fastcall" || valof(x) == "thiscall" || valof(x) == "llvmcall") && is_in_fexpr(x, x->iscall(x) && isidentifier(x.args[1]) && valof(x.args[1]) == "ccall"))
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
        return refof(x.args[2].args[1])
    end
end

function should_mark_missing_getfield_ref(x, server)
    if isidentifier(x) && !hasref(x) && # x has no ref
    parentof(x) isa EXPR && headof(parentof(x)) === :quotenode && parentof(parentof(x)) isa EXPR && is_getfield(parentof(parentof(x)))  # x is the rhs of a getproperty
        lhsref = refof_maybe_getfield(parentof(parentof(x)).args[1])
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
                !(t isa SymbolServer.FakeUnion) && t.name == b.name.name && return true
            end
        end
    else
        for m in getsymbolserver(server)[:Base][:getproperty].methods
            t = unwrap_fakeunionall(m.sig[1][2])
            !(t isa SymbolServer.FakeUnion) && t.name == b.name.name && return true
        end
    end
    return false
end

function has_getproperty_method(b::Binding)
    if b.val isa Binding
        return has_getproperty_method(b.val)
    elseif b.val isa SymbolServer.DataTypeStore
        return has_getproperty_method(b.val)
    elseif b isa Binding && b.type === CoreTypes.DataType
        safety_trip = 0
        while b !== nothing
            safety_trip += 1
            if safety_trip > 1000
                error("Infinite loop.")
            end
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
        if iscall(x)
            func_name = x.args[1]
            return (isidentifier(func_name) && valof(func_name) == "getproperty") || # getproperty()
            (is_getfield_w_quotenode(func_name) && isidentifier(func_name.args[2].args[1]) && valof(func_name.args[2].args[1]) == "getproperty") # Base.getproperty()
        end
        return false
    end

    return parentof(x) isa EXPR && parentof(parentof(x)) isa EXPR &&
        ((isdeclaration(parentof(x)) && x === parentof(x).args[2] && is_call_to_getproperty(parentof(parentof(x)))) ||
        (iscurly(parentof(x)) && x === parentof(x).args[1] && isdeclaration(parentof(parentof(x))) &&  parentof(parentof(parentof(x))) isa EXPR && is_call_to_getproperty(parentof(parentof(parentof(x))))))
end

isunionfaketype(t::SymbolServer.FakeTypeName) = t.name.name === :Union && t.name.parent isa SymbolServer.VarRef && t.name.parent.name === :Core

function check_typeparams(x::EXPR)
    if iswhere(x)
        for i in 2:length(x.args)
            a = x.args[i]
            if hasbinding(a) && (bindingof(a).refs === nothing || length(bindingof(a).refs) < 2)
                seterror!(a, UnusedTypeParameter)
            end
        end
    end
end

function check_for_pirates(x::EXPR)
    if CSTParser.defines_function(x)
        sig = CSTParser.rem_where_decl(CSTParser.get_sig(x))
        if fname_is_noteq(CSTParser.get_name(sig))
            seterror!(x, NotEqDef)
        elseif iscall(sig) && hasbinding(x) && overwrites_imported_function(bindingof(x))
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

function fname_is_noteq(x)
    if x isa EXPR
        if isoperator(x) && valof(x) == "!="
            return true
        elseif is_getfield_w_quotenode(x)
            return fname_is_noteq(x.args[2].args[1])
        end
    end
    return false
end

function refers_to_nonimported_type(arg::EXPR)
    arg = CSTParser.rem_wheres(arg)
    if hasref(arg) && refof(arg) isa Binding
        return true
    elseif isunarysyntax(arg) && (valof(headof(arg)) == "::" || valof(headof(arg)) == "<:")
        return refers_to_nonimported_type(arg.args[1])
    elseif isdeclaration(arg)
        return refers_to_nonimported_type(arg.args[2])
    elseif iscurly(arg)
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
        elseif (b.prev.val isa SymbolServer.FunctionStore || b.prev.val isa SymbolServer.DataTypeStore) && parentof(b.prev.name) isa EXPR && is_in_fexpr(parentof(b.prev.name), x -> headof(x) === :import)
            # last expr of above condition can be improved on (more restrictive inspection of parent exprs).
            # explicitly imported, e.g. import ModuleName: somefunction
            return true
        end
    elseif b.prev isa SymbolServer.FunctionStore &&
        parentof(b.name) isa EXPR && headof(parentof(b.name)) === :quotenode && is_getfield(parentof(parentof(b.name)))
        fullname = parentof(parentof(b.name))
        # overwrites imported function by declaring full name, e.g. ModuleName.FunctionName
        if isidentifier(fullname.args[1]) && refof(fullname.args[1]) isa SymbolServer.ModuleStore
            return true
        elseif is_getfield(fullname.args[1]) && headof(fullname.args[1].args[2]) === :quotenode && refof(fullname.args[1].args[2].args[1]) isa SymbolServer.ModuleStore
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


"""
    check_kw_default(x::EXPR, server)

Check that the default value matches the type for keyword arguments. Following types are
checked: `String, Symbol, Int, Char, Bool, Float32, Float64, UInt8, UInt16, UInt32,
UInt64, UInt128`.
"""
function check_kw_default(x::EXPR, server)
    if headof(x) == :kw && isdeclaration(x.args[1]) && CSTParser.isliteral(x.args[2]) && hasref(x.args[1].args[2])
        decl_T = refof(x.args[1].args[2])
        rhs = x.args[2]
        rhsval = valof(rhs)
        if decl_T == getsymbolserver(server)[:Core][:String] && !CSTParser.isstringliteral(rhs)
            seterror!(rhs, KwDefaultMismatch)
        elseif decl_T == getsymbolserver(server)[:Core][:Symbol] && headof(rhs) !== :IDENTIFIER
            seterror!(rhs, KwDefaultMismatch)
        elseif decl_T == getsymbolserver(server)[:Core][:Int] && headof(rhs) !== :INTEGER
            seterror!(rhs, KwDefaultMismatch)
        elseif decl_T == getsymbolserver(server)[:Core][Sys.WORD_SIZE == 64 ? :Int64 : :Int32] && headof(rhs) !== :INTEGER
            seterror!(rhs, KwDefaultMismatch)
        elseif decl_T == getsymbolserver(server)[:Core][:Bool] && !(headof(rhs) === :TRUE || headof(rhs) === :FALSE)
            seterror!(rhs, KwDefaultMismatch)
        elseif decl_T == getsymbolserver(server)[:Core][:Char] && headof(rhs) !== :CHAR
            seterror!(rhs, KwDefaultMismatch)
        elseif decl_T == getsymbolserver(server)[:Core][:Float64] && headof(rhs) !== :FLOAT
            seterror!(rhs, KwDefaultMismatch)
        elseif decl_T == getsymbolserver(server)[:Core][:Float32] && !(headof(rhs) === :FLOAT && occursin("f", rhsval))
            seterror!(rhs, KwDefaultMismatch)
        else
            for T in (UInt8, UInt16, UInt32, UInt64, UInt128)
                if decl_T == getsymbolserver(server)[:Core][Symbol(T)]
                    # count the digits without prefix (=0x, 0o, 0b) and make sure it fits
                    # between upper and lower literal boundaries for `T` where the boundaries
                    # depend on the type of literal (binary, octal, hex)
                    n = count(x -> x != '_', rhsval) - 2
                    ub = sizeof(T)
                    lb = ub ÷ 2
                    if headof(rhs) == :BININT
                        8lb < n <= 8ub || seterror!(rhs, KwDefaultMismatch)
                    elseif headof(rhs) == :OCTINT
                        3lb < n <= 3ub || seterror!(rhs, KwDefaultMismatch)
                    elseif headof(rhs) == :HEXINT
                        2lb < n <= 2ub || seterror!(rhs, KwDefaultMismatch)
                    else
                        seterror!(rhs, KwDefaultMismatch)
                    end
                end
            end
            # signed integers of non native size can't be declared as literal
            for T in (Int8, Int16, Sys.WORD_SIZE == 64 ? Int32 : Int64, Int128)
                if decl_T == getsymbolserver(server)[:Core][Symbol(T)]
                    seterror!(rhs, KwDefaultMismatch)
                end
            end

        end
    end
end

function check_use_of_literal(x::EXPR)
    if CSTParser.defines_module(x) && length(x.args) > 1 && isbadliteral(x.args[2])
        seterror!(x.args[2], InappropriateUseOfLiteral)
    elseif (CSTParser.defines_abstract(x) || CSTParser.defines_primitive(x)) && isbadliteral(x.args[1])
        seterror!(x.args[1], InappropriateUseOfLiteral)
    elseif CSTParser.defines_struct(x) && isbadliteral(x.args[2])
            seterror!(x.args[2], InappropriateUseOfLiteral)
    elseif (isassignment(x) || iskwarg(x)) && isbadliteral(x.args[1])
        seterror!(x.args[1], InappropriateUseOfLiteral)
    elseif isdeclaration(x) && isbadliteral(x.args[2])
        seterror!(x.args[2], InappropriateUseOfLiteral)
    elseif isbinarycall(x, "isa") && isbadliteral(x.args[3])
        seterror!(x.args[3], InappropriateUseOfLiteral)
    end
end

isbadliteral(x::EXPR) = CSTParser.isliteral(x) && (CSTParser.isstringliteral(x) || headof(x) === :INTEGER || headof(x) === :FLOAT || headof(x) === :CHAR || headof(x) === :TRUE || headof(x) === :FALSE)

function check_break_continue(x::EXPR)
    if iskeyword(x) && (headof(x) === :CONTINUE || headof(x) === :BREAK) && !is_in_fexpr(x, x -> headof(x) in (:for, :while))
        seterror!(x, ShouldBeInALoop)
    end
end



