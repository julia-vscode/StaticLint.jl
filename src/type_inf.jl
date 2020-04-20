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

fieldname_type_map(s, server, l = Dict()) = l # fallback
function fieldname_type_map(s::Scope, server, l = Dict())
    for (n,b) in s.names
        b = get_root_method(b, server)
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
    l
end

function fieldname_type_map(cache::SymbolServer.ModuleStore, l)
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
    l
end

function fieldname_type_map(cache::SymbolServer.EnvStore, l = Dict())
    for (_,m) in cache
        fieldname_type_map(m, l)
    end
    l
end

function infer_type_by_getfield_calls(b::Binding, server)
    b.type !== nothing && return # b already has a type
    user_datatypes = fieldname_type_map(retrieve_toplevel_scope(b.val), server)
    possibletypes = []
    for ref in b.refs
        ref isa EXPR || continue # skip non-EXPR (i.e. used for handling of globals)
        if is_getfield_lhs(ref) && typof(parentof(ref)[3]) === CSTParser.Quotenode
            rhs = parentof(ref)[3][1]
        elseif is_getfield_lhs_as_chain(ref)
            rhs = parentof(parentof(parentof(ref)))[3][1]
        else
            continue
        end
        
        if isidentifier(rhs)
            rhs_sym = Symbol(CSTParser.str_value(rhs))
            new_possibles = [get(getsymbolfieldtypemap(server), rhs_sym, [])..., get(user_datatypes, rhs_sym, [])...]

            # @info new_possibles
            if isempty(possibletypes)
                possibletypes = new_possibles
            elseif !isempty(new_possibles)
                possibletypes = intersect(possibletypes, new_possibles)
            end
            if isempty(possibletypes)
                return
            end
        end
    end
    if length(possibletypes) == 1
        type = first(possibletypes)
        if type isa Binding
            b.type = type
        elseif type isa SymbolServer.VarRef
            b.type = SymbolServer._lookup(type, getsymbolserver(server)) # could be nothing
        else
        end
    end
end


