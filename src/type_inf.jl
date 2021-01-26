function infer_type(binding::Binding, scope, state)
    if binding isa Binding
        binding.type !== nothing && return
        if binding.val isa EXPR && CSTParser.defines_module(binding.val)
            binding.type = CoreTypes.Module
        elseif binding.val isa EXPR && CSTParser.defines_function(binding.val)
            binding.type = CoreTypes.Function
        elseif binding.val isa EXPR && CSTParser.defines_datatype(binding.val)
            binding.type = CoreTypes.DataType
        elseif binding.val isa EXPR
            if isassignment(binding.val)
                if CSTParser.is_func_call(binding.val.args[1])
                    binding.type = CoreTypes.Function
                else
                    infer_type_assignment_rhs(binding, state, scope)
                end
            elseif binding.val.head isa EXPR && valof(binding.val.head) == "::"
                infer_type_decl(binding, state, scope)
            end
        end
    end
end

function infer_type_assignment_rhs(binding, state, scope)
    rhs = binding.val.args[2]
    if CSTParser.is_func_call(rhs)
        callname = CSTParser.get_name(rhs)
        if isidentifier(callname)
            resolve_ref(callname, scope, state)
            if hasref(callname)
                rb = get_root_method(refof(callname), state.server)
                if (rb isa Binding && (rb.type == CoreTypes.DataType || rb.val isa SymbolServer.DataTypeStore)) || rb isa SymbolServer.DataTypeStore
                    binding.type = rb
                end
            end
        end
    elseif headof(rhs) === :INTEGER
        binding.type = CoreTypes.Int
    elseif headof(rhs) === :FLOAT
        binding.type = CoreTypes.Float64
    elseif CSTParser.isstringliteral(rhs)
        binding.type = CoreTypes.String
    elseif isidentifier(rhs) || is_getfield_w_quotenode(rhs)
        refof_rhs = isidentifier(rhs) ? refof(rhs) : refof_maybe_getfield(rhs)
        if refof_rhs isa Binding
            rhs_bind = refof(rhs)
            if refof_rhs.val isa SymbolServer.GenericStore && refof_rhs.val.typ isa SymbolServer.FakeTypeName
                binding.type = maybe_lookup(refof_rhs.val.typ.name, state.server)
            elseif refof_rhs.val isa SymbolServer.FunctionStore
                binding.type = CoreTypes.Function
            elseif refof_rhs.val isa SymbolServer.DataTypeStore
                binding.type = CoreTypes.DataType
            else
                binding.type = refof_rhs.type
            end
        elseif refof_rhs isa SymbolServer.GenericStore && refof_rhs.typ isa SymbolServer.FakeTypeName
            binding.type = maybe_lookup(refof_rhs.typ.name, state.server)
        elseif refof_rhs isa SymbolServer.FunctionStore
            binding.type = CoreTypes.Function
        elseif refof_rhs isa SymbolServer.DataTypeStore
            binding.type = CoreTypes.DataType
        end
    end
end

function infer_type_decl(binding, state, scope)
    t = binding.val.args[2]
    if isidentifier(t)
        resolve_ref(t, scope, state)
    end
    if iscurly(t)
        t = t.args[1]
        resolve_ref(t, scope, state)
    end
    if CSTParser.is_getfield_w_quotenode(t)
        resolve_getfield(t, scope, state)
        t = t.args[2].args[1]
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

# Work out what type a bound variable has by functions that are called on it.
function infer_type_by_use(b::Binding, env::ExternalEnv)
    b.type !== nothing && return # b already has a type
    possibletypes = []
    visitedmethods = []
    for ref in b.refs
        new_possibles = []
        ref isa EXPR || continue # skip non-EXPR (i.e. used for handling of globals)
        check_ref_against_calls(ref, visitedmethods, new_possibles, env)

        if isempty(possibletypes)
            possibletypes = new_possibles
        elseif !isempty(new_possibles)
            possibletypes = intersect(possibletypes, new_possibles)
            if isempty(possibletypes)
                return
            end
        end
    end
    # Only do something if we're left with a singleton set at the end.
    if length(possibletypes) == 1
        type = first(possibletypes)
    
        if type isa Binding
            b.type = type
        elseif type isa SymbolServer.DataTypeStore
            b.type = type
        elseif type isa SymbolServer.VarRef
            b.type = SymbolServer._lookup(type, getsymbols(env)) # could be nothing
        elseif type isa SymbolServer.FakeTypeName && isempty(type.parameters)
            b.type = SymbolServer._lookup(type.name, getsymbols(env)) # could be nothing
        end
    end
end

function check_ref_against_calls(x, visitedmethods, new_possibles, env::ExternalEnv)
    if is_arg_of_resolved_call(x)
        sig = parentof(x)
        # x is argument of function call (func) and we know what that function is
        if CSTParser.isidentifier(sig.args[1])
            func = refof(sig.args[1])
        else
            func = refof(sig.args[1].args[2].args[1])
        end
        argi = get_arg_position_in_call(sig, x) # what slot does ref sit in?
        tls = retrieve_toplevel_scope(x)
        if func isa Binding
            for method in func.refs
                method = get_method(method)
                method === nothing && continue
                if method isa EXPR 
                    if defines_function(method)
                        get_arg_type_at_position(method, argi, new_possibles)
                    # elseif CSTParser.defines_struct(method)
                        # Can we ignore this? Default constructor gives us no type info?
                    end
                else # elseif what? 
                    iterate_over_ss_methods(method, tls, env, m -> (get_arg_type_at_position(m, argi, new_possibles);false))
                end
            end
        else
            iterate_over_ss_methods(func, tls, env, m -> (get_arg_type_at_position(m, argi, new_possibles);false))
        end
    end
end

function is_arg_of_resolved_call(x::EXPR) 
    parentof(x) isa EXPR && headof(parentof(x)) === :call && # check we're in a call signature
    (caller = parentof(x).args[1]) !== x && # and that x is not the caller
    ((CSTParser.isidentifier(caller) && hasref(caller)) || (is_getfield(caller) && headof(caller.args[2]) === :quotenode && hasref(caller.args[2].args[1])))
end

function get_arg_position_in_call(sig::EXPR, arg)
    for i in 1:length(sig.args)
        sig.args[i] == arg && return i
    end
end

function get_arg_type_at_position(method, argi, types)
    if method isa EXPR
        sig = CSTParser.get_sig(method)
        if sig !== nothing && 
            sig.args !== nothing && argi <= length(sig.args) &&
            hasbinding(sig.args[argi]) &&
            (argb = bindingof(sig.args[argi]); argb isa Binding && argb.type !== nothing) && 
            !(argb.type in types)
            push!(types, argb.type)
            return
        end
    elseif method isa SymbolServer.DataTypeStore || method isa SymbolServer.FunctionStore
        for m in method.methods
            get_arg_type_at_position(m, argi, types)
        end
    end
    return
end

function get_arg_type_at_position(m::SymbolServer.MethodStore, argi, types)
    if length(m.sig) >= argi && m.sig[argi][2] != SymbolServer.VarRef(SymbolServer.VarRef(nothing, :Core), :Any) && !(m.sig[argi][2] in types)
        push!(types, m.sig[argi][2])
    end
end
