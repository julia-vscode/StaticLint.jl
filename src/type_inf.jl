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
