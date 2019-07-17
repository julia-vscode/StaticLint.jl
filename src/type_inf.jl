function infer_type(binding::CSTParser.Binding, scope, server)
    if binding isa CSTParser.Binding
        binding.t !== nothing && return
        if binding.val isa EXPR && (typof(binding.val) === CSTParser.ModuleH || typof(binding.val) === CSTParser.BareModule)
            binding.t = getsymbolserver(server)["Core"].vals["Module"]
        elseif binding.val isa EXPR && typof(binding.val) === CSTParser.FunctionDef
            binding.t = getsymbolserver(server)["Core"].vals["Function"]
        elseif binding.val isa EXPR && (typof(binding.val) === CSTParser.Struct || typof(binding.val) === CSTParser.Mutable || typof(binding.val) === CSTParser.Abstract  || typof(binding.val) === CSTParser.Primitive)
            binding.t = getsymbolserver(server)["Core"].vals["DataType"]
        elseif binding.val isa EXPR && typof(binding.val) === BinaryOpCall
            if kindof(binding.val.args[2]) === CSTParser.Tokens.EQ
                if CSTParser.is_func_call(binding.val.args[1])
                    binding.t = getsymbolserver(server)["Core"].vals["Function"]
                elseif CSTParser.is_func_call(binding.val.args[3])
                    callname = CSTParser.get_name(binding.val.args[3])
                    if CSTParser.isidentifier(callname)
                        resolve_ref(callname, scope)
                        if hasref(callname)
                            rb = get_root_method(refof(callname), server)
                            if (rb isa Binding && (rb.t == getsymbolserver(server)["Core"].vals["DataType"] || rb.val isa SymbolServer.structStore)) || rb isa SymbolServer.structStore
                                binding.t = rb
                            end
                        end
                    end
                elseif kindof(binding.val.args[3]) === CSTParser.Tokens.INTEGER
                    binding.t = getsymbolserver(server)["Core"].vals["Int"]
                elseif kindof(binding.val.args[3]) === CSTParser.Tokens.FLOAT
                    binding.t = getsymbolserver(server)["Core"].vals["Float64"]
                elseif kindof(binding.val.args[3]) === CSTParser.Tokens.STRING || typof(binding.val.args[3]) === CSTParser.Tokens.TRIPLE_STRING
                    binding.t = getsymbolserver(server)["Core"].vals["String"]
                elseif typof(binding.val.args[3]) === IDENTIFIER && refof(binding.val.args[3]) isa CSTParser.Binding
                    binding.t = refof(binding.val.args[3]).t
                end
            elseif kindof(binding.val.args[2]) === CSTParser.Tokens.DECLARATION
                t = binding.val.args[3]
                if CSTParser.isidentifier(t)
                    resolve_ref(t, scope)
                end
                if typof(t) === CSTParser.Curly
                    t = t.args[1]
                    resolve_ref(t, scope)
                end
                if typof(t) === CSTParser.BinaryOpCall && kindof(t.args[2]) === CSTParser.Tokens.DOT && t.args[3].args isa Vector && length(t.args[3].args) > 0
                    t = t.args[3].args[1]
                end             

                if refof(t) isa CSTParser.Binding
                    rb = get_root_method(refof(t), server)
                    if rb isa Binding && rb.t == getsymbolserver(server)["Core"].vals["DataType"]
                        binding.t = rb
                    else
                        binding.t = refof(t)
                    end
                end
            end
        end
    end
end
