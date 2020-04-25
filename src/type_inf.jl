function infer_type(binding::Binding, scope, state)
    if binding isa Binding
        binding.type !== nothing && return
        if binding.val isa EXPR && (typof(binding.val) === CSTParser.ModuleH || typof(binding.val) === CSTParser.BareModule)
            binding.type = CoreTypes.Module
        elseif binding.val isa EXPR && typof(binding.val) === CSTParser.FunctionDef
            binding.type = CoreTypes.Function
        elseif binding.val isa EXPR && (typof(binding.val) === CSTParser.Struct || typof(binding.val) === CSTParser.Mutable || typof(binding.val) === CSTParser.Abstract  || typof(binding.val) === CSTParser.Primitive)
            binding.type = CoreTypes.DataType
        elseif binding.val isa EXPR && typof(binding.val) === BinaryOpCall
            if kindof(binding.val[2]) === CSTParser.Tokens.EQ
                if CSTParser.is_func_call(binding.val[1])
                    binding.type = CoreTypes.Function
                elseif CSTParser.is_func_call(binding.val[3])
                    callname = CSTParser.get_name(binding.val[3])
                    if CSTParser.isidentifier(callname)
                        resolve_ref(callname, scope, state, [])
                        if hasref(callname)
                            rb = get_root_method(refof(callname), state.server)
                            if (rb isa Binding && (rb.type == CoreTypes.DataType || rb.val isa SymbolServer.DataTypeStore)) || rb isa SymbolServer.DataTypeStore
                                binding.type = rb
                            end
                        end
                    end
                elseif kindof(binding.val[3]) === CSTParser.Tokens.INTEGER
                    binding.type = CoreTypes.Int
                elseif kindof(binding.val[3]) === CSTParser.Tokens.FLOAT
                    binding.type = CoreTypes.Float64
                elseif kindof(binding.val[3]) === CSTParser.Tokens.STRING || typof(binding.val[3]) === CSTParser.Tokens.TRIPLE_STRING
                    binding.type = CoreTypes.String
                elseif typof(binding.val[3]) === IDENTIFIER && refof(binding.val[3]) isa Binding
                    binding.type = refof(binding.val[3]).type
                end
            elseif kindof(binding.val[2]) === CSTParser.Tokens.DECLARATION
                t = binding.val[3]
                if CSTParser.isidentifier(t)
                    resolve_ref(t, scope, state, [])
                end
                if typof(t) === CSTParser.Curly
                    t = t[1]
                    resolve_ref(t, scope, state, [])
                end
                if is_getfield(t) && length(t[3]) > 0
                    t = t[3][1]
                    resolve_ref(t, scope, state, [])
                end

                if refof(t) isa Binding
                    rb = get_root_method(refof(t), state.server)
                    if rb isa Binding && rb.type == CoreTypes.DataType
                        binding.type = rb
                    else
                        binding.type = refof(t)
                    end
                elseif refof(t) isa SymbolServer.DataTypeStore
                    binding.type = refof(t)
                end
            end
        elseif binding.val isa EXPR && parentof(binding.val) isa EXPR && typof(parentof(binding.val)) === CSTParser.WhereOpCall
            binding.type = CoreTypes.DataType
        end
    end
end

"""
    is_getfield_lhs(x::EXPR)
x the `a` in `a.b`
"""
is_getfield_lhs(x::EXPR) = is_getfield(parentof(x)) && x === parentof(x)[1]

"""
    is_getfield_lhs_as_chain(x::EXPR)
x the `b` in `a.b.c`
"""
is_getfield_lhs_as_chain(x::EXPR) = parentof(x) isa EXPR && typof(parentof(x)) === CSTParser.Quotenode && StaticLint.is_getfield(parentof(parentof(x))) && StaticLint.is_getfield(parentof(parentof(parentof(x)))) && x === parentof(parentof(x))[3][1]

isemptyvect(x::EXPR) = typof(x) === CSTParser.Vect && length(x) == 2

function get_struct_fieldname(x::EXPR)
    if _binary_assert(x, CSTParser.Tokens.DECLARATION)
        return get_struct_fieldname(x[1])
    elseif typof(x) === CSTParser.InvisBrackets && length(x) == 3
        return get_struct_fieldname(x[2])
    elseif isidentifier(x)
        return x
    else
    end
    return nothing
end

function cst_struct_fieldnames(x::EXPR)
    fns = Symbol[]
    if CSTParser.defines_mutable(x)
        body = x[4]
    elseif CSTParser.defines_struct(x)
        body = x[3]
    else
        return fns
    end
    for arg in body
        field_name = get_struct_fieldname(arg)
        if field_name isa EXPR && isidentifier(field_name)
            push!(fns, Symbol(CSTParser.str_value(field_name)))
        end
    end
    return fns
end


"""
    fieldname_type_map(s::Union{Scope,ModuleStore,EnvStore}, server, l = Dict())

Returns a Dict where a fieldname (key) points to a collection of types that 
have that field. 
"""
fieldname_type_map(s, server, l = Dict{Symbol,Any}()) = l # fallback
function fieldname_type_map(s::Scope, server, l = Dict())
    for (n,b) in s.names
        b = get_root_method(b, server)
        # Todo: Allow for const rebindings of datatypes (i.e. `const dt = DataType`)
        if b isa Binding && b.val isa EXPR && CSTParser.defines_datatype(b.val)
            for f in cst_struct_fieldnames(b.val)
                f = Symbol(f)
                if haskey(l, f)
                    push!(l[f], b)
                else
                    l[f] = [b]
                end
            end
        end
    end
    return l
end

function fieldname_type_map(cache::SymbolServer.ModuleStore, l = Dict{Symbol,Any}())
    for (n,v) in cache.vals
        if v isa SymbolServer.DataTypeStore
            for f in v.fieldnames
                if haskey(l, f)
                    push!(l[f], v.name.name)
                else
                    l[f] = [v.name.name]
                end
            end
        elseif v isa SymbolServer.ModuleStore
            fieldname_type_map(v, l)
        end
    end
    return l
end

function fieldname_type_map(cache::SymbolServer.EnvStore, l = Dict{Symbol,Any}())
    for (_,m) in cache
        fieldname_type_map(m, l)
    end
    return l
end

"""
    check_ref_against_fieldnames(ref, user_datatypes, new_possibles, server)

Tries to infer the type of `ref` by looking at how getfield is used against it
and comparing these instances against the fields of all known datatypes. These
are pre-cached for packages in the server's EnvStore (`getsymbolfieldtypemap(server)`).
"""
function check_ref_against_fieldnames(ref, user_datatypes, new_possibles, server)
    if is_getfield_lhs(ref) && typof(parentof(ref)[3]) === CSTParser.Quotenode
        rhs = parentof(ref)[3][1]
    elseif is_getfield_lhs_as_chain(ref)
        rhs = parentof(parentof(parentof(ref)))[3][1]
    else
        return
    end
    if isidentifier(rhs)
        rhs_sym = Symbol(CSTParser.str_value(rhs))
        for t in get(getsymbolfieldtypemap(server), rhs_sym, [])
            push!(new_possibles, t)
        end
        for t in get(user_datatypes, rhs_sym, [])
            push!(new_possibles, t)
        end
    end
end

"""
    is_arg_of_resolved_call(x)

Checks whether x is the argument of a function call.
"""
is_arg_of_resolved_call(x::EXPR) = parentof(x) isa EXPR && typof(parentof(x)) === Call && parentof(x)[1] !== x &&
(hasref(parentof(x)[1]) || (is_getfield(parentof(x)[1]) && typof(parentof(x)[1][3]) === CSTParser.Quotenode && hasref(parentof(x)[1][3][1])))


"""
    get_arg_position_in_call(call, arg)
    get_arg_position_in_call(arg)

Returns the position of `arg` in `call` ignoring the function name and punctuation.
The single argument method assumes `parentof(arg) == call`
"""
function get_arg_position_in_call(call::EXPR, arg)
    for (i,a) in enumerate(call)
        a == arg && return div(i-1, 2) 
    end
end

function get_arg_position_in_call(arg)
    get_arg_position_in_call(parentof(arg), arg)
end


"""
    get_arg_type_at_position(f, argi, types)

Pushes to `types` the argument type (if not `Core.Any`) of a function
at position `argi`.
"""
function get_arg_type_at_position(f, argi, types) end

function get_arg_type_at_position(b::Binding, argi, types)
    argi1 = argi*2 + 1
    if b.val isa EXPR
        sig = CSTParser.get_sig(b.val)
        if sig !== nothing && 
            argi1 < length(sig) &&
            hasbinding(sig[argi1]) &&
            (argb = bindingof(sig[argi1]); argb isa Binding && argb.type !== nothing) && 
            !(argb.type in types)
            push!(types, argb.type)
            return
        end
    elseif b.val isa SymbolServer.SymStore
        return get_arg_type_at_position(b.val, argi, types)
    end
    return
end

function get_arg_type_at_position(f::T, argi, types) where T <: Union{SymbolServer.DataTypeStore,SymbolServer.FunctionStore}
    for m in f.methods
        get_arg_type_at_position(m, argi, types)
    end
end

function get_arg_type_at_position(m::SymbolServer.MethodStore, argi, types)
    if length(m.sig) >= argi && m.sig[argi][2] != SymbolServer.VarRef(SymbolServer.VarRef(nothing, :Core), :Any) && !(m.sig[argi][2] in types)
        push!(types, m.sig[argi][2])
    end
end

"""
    check_ref_against_calls(x, visitedmethods, new_possibles, server)

Pushes to `new_possibles`
"""
function check_ref_against_calls(x, visitedmethods, new_possibles, server)
    if is_arg_of_resolved_call(x)
        # x is argument of function call (func) and we know what that function is
        if CSTParser.isidentifier(parentof(x)[1])
            func = refof(parentof(x)[1])
        else
            func = refof(parentof(x)[1][3][1])
        end
        # make sure we've got the last binding for func
        if func isa Binding
            func = get_last_method(func, server)
        end
        # what slot does ref sit in?
        argi = get_arg_position_in_call(x)
        tls = retrieve_toplevel_scope(x)
        while (func isa Binding && func.type == CoreTypes.Function) || func isa SymbolServer.SymStore
            !(func in visitedmethods) ? push!(visitedmethods, func) : return # check whether we've been here before
            if func isa Binding
                get_arg_type_at_position(func, argi, new_possibles)
                func = prev_method(func)
            else
                tls === nothing && return
                iterate_over_ss_methods(func, tls, server, m->(get_arg_type_at_position(m, argi, new_possibles);false))
                return
            end
        end
    end
end

"""
    infer_type_by_use(b::Binding, server)

Tries to infer the type of Binding `b` by looking at how it is used.
"""
function infer_type_by_use(b::Binding, server)
    b.type !== nothing && return # b already has a type
    user_datatypes = fieldname_type_map(retrieve_toplevel_scope(b.val), server)
    possibletypes = []
    visitedmethods = []
    for ref in b.refs
        new_possibles = []
        ref isa EXPR || continue # skip non-EXPR (i.e. used for handling of globals)
        check_ref_against_fieldnames(ref, user_datatypes, new_possibles, server)
        check_ref_against_calls(ref, visitedmethods, new_possibles, server)

        if isempty(possibletypes)
            possibletypes = new_possibles
        elseif !isempty(new_possibles)
            possibletypes = intersect(possibletypes, new_possibles)
            if isempty(possibletypes)
                return
            end
        end
    end
    # Only do something if we're left with a set of 1 at the end.
    if length(possibletypes) == 1
        type = first(possibletypes)
        if type isa Binding
            b.type = type
        elseif type isa SymbolServer.DataTypeStore
            b.type = type
        elseif type isa SymbolServer.VarRef
            b.type = SymbolServer._lookup(type, getsymbolserver(server)) # could be nothing
        elseif type isa SymbolServer.FakeTypeName && isempty(type.parameters)
            b.type = SymbolServer._lookup(type.name, getsymbolserver(server)) # could be nothing
        end
    end
end

"""
    isrebinding(b::Binding)

Does `b` simply rebind another binding? 
"""
function isrebinding(b::Binding)
    b.val isa EXPR && CSTParser.is_assignment(b.val) && 
    b.val[1] == b.name && CSTParser.isidentifier(b.val[3]) &&
    hasbinding(b.val[3])
end

"""
    getrebound(b::Binding)

Assumes `isrebinding(b) == true` and gets the source binding (recursively).
"""
getrebound(b::Binding) = isrebinding(bindingof(b.val[3])) ? getrebound(bindingof(b.val[3])) : bindingof(b.val[3])
