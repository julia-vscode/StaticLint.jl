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
                if CSTParser.is_func_call(binding.val[1])
                    binding.type = CoreTypes.Function
                elseif CSTParser.is_func_call(binding.val[3])
                    callname = CSTParser.get_name(binding.val[3])
                    if isidentifier(callname)
                        resolve_ref(callname, scope, state)
                        if hasref(callname)
                            rb = get_root_method(refof(callname), state.server)
                            if (rb isa Binding && (rb.type == CoreTypes.DataType || rb.val isa SymbolServer.DataTypeStore)) || rb isa SymbolServer.DataTypeStore
                                binding.type = rb
                            end
                        end
                    end
                elseif headof(binding.val[3]) === :INTEGER
                    binding.type = CoreTypes.Int
                elseif headof(binding.val[3]) === :FLOAT
                    binding.type = CoreTypes.Float64
                elseif CSTParser.isstringliteral(binding.val[3])
                    binding.type = CoreTypes.String
                elseif isidentifier(binding.val[3]) && refof(binding.val[3]) isa Binding
                    binding.type = refof(binding.val[3]).type
                end
            elseif binding.val.head isa EXPR && valof(binding.val.head) === "::"
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
        end
    end
end
