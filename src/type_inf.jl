function infer_type(binding::CSTParser.Binding, scope, server)
    if binding isa CSTParser.Binding
        binding.t !== nothing && return
        if binding.val isa EXPR && (binding.val.typ === CSTParser.ModuleH || binding.val.typ === CSTParser.BareModule)
            binding.t = getsymbolserver(server)["Core"].vals["Module"]
        elseif binding.val isa EXPR && binding.val.typ === CSTParser.FunctionDef
            binding.t = getsymbolserver(server)["Core"].vals["Function"]
        elseif binding.val isa EXPR && (binding.val.typ === CSTParser.Struct || binding.val.typ === CSTParser.Mutable || binding.val.typ === CSTParser.Abstract  || binding.val.typ === CSTParser.Primitive)
            binding.t = getsymbolserver(server)["Core"].vals["DataType"]
        elseif binding.val isa EXPR && binding.val.typ === BinaryOpCall
            if binding.val.args[2].kind === CSTParser.Tokens.EQ
                if CSTParser.is_func_call(binding.val.args[1])
                    binding.t = getsymbolserver(server)["Core"].vals["Function"]
                elseif CSTParser.is_func_call(binding.val.args[3])
                    callname = CSTParser.get_name(binding.val.args[3])
                    if CSTParser.isidentifier(callname)
                        resolve_ref(callname, scope)
                        if hasref(callname)
                            rb = get_root_method(callname.ref, server)
                            if (rb isa Binding && (rb.t == getsymbolserver(server)["Core"].vals["DataType"] || rb.val isa SymbolServer.structStore)) || rb isa SymbolServer.structStore
                                binding.t = rb
                            end
                        end
                    end
                elseif binding.val.args[3].kind === CSTParser.Tokens.INTEGER
                    binding.t = getsymbolserver(server)["Core"].vals["Int"]
                elseif binding.val.args[3].kind === CSTParser.Tokens.FLOAT
                    binding.t = getsymbolserver(server)["Core"].vals["Float64"]
                elseif binding.val.args[3].kind === CSTParser.Tokens.STRING || binding.val.args[3].typ === CSTParser.Tokens.TRIPLE_STRING
                    binding.t = getsymbolserver(server)["Core"].vals["String"]
                elseif binding.val.args[3].typ === IDENTIFIER && binding.val.args[3].ref isa CSTParser.Binding
                    binding.t = binding.val.args[3].ref.t
                end
            elseif binding.val.args[2].kind === CSTParser.Tokens.DECLARATION
                t = binding.val.args[3]
                if CSTParser.isidentifier(t)
                    resolve_ref(t, scope)
                end
                if t.typ === CSTParser.Curly
                    t = t.args[1]
                    resolve_ref(t, scope)
                end
                if t.typ === CSTParser.BinaryOpCall && t.args[2].kind === CSTParser.Tokens.DOT && t.args[3].args isa Vector && length(t.args[3].args) > 0
                    t = t.args[3].args[1]
                end             

                if t.ref isa CSTParser.Binding
                    rb = get_root_method(t.ref, server)
                    if rb isa Binding && rb.t == getsymbolserver(server)["Core"].vals["DataType"]
                        binding.t = rb
                    else
                        binding.t = t.ref
                    end
                end
            end
        end
    end
end
