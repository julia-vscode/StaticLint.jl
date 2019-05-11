function infer_type(binding::CSTParser.Binding, server)
    if binding isa CSTParser.Binding
        if binding.val isa EXPR && (binding.val.typ === CSTParser.ModuleH || binding.val.typ === CSTParser.BareModule)
            binding.t = getsymbolserver(server)["Core"].vals["Module"]
        elseif binding.val isa EXPR && binding.val.typ === CSTParser.FunctionDef
            binding.t = getsymbolserver(server)["Core"].vals["Function"]
        elseif binding.val isa EXPR && binding.val.typ === BinaryOpCall
            if binding.val.args[2].kind === CSTParser.Tokens.EQ
                if binding.val.args[3].kind === CSTParser.Tokens.INTEGER
                    binding.t = getsymbolserver(server)["Core"].vals["Int"]
                elseif binding.val.args[3].kind === CSTParser.Tokens.FLOAT
                    binding.t = getsymbolserver(server)["Core"].vals["Float64"]
                elseif binding.val.args[3].kind === CSTParser.Tokens.STRING || binding.val.args[3].typ === CSTParser.Tokens.TRIPLE_STRING
                    binding.t = getsymbolserver(server)["Core"].vals["String"]
                elseif binding.val.args[3].typ === IDENTIFIER && binding.val.args[3].ref isa CSTParser.Binding
                    binding.t = binding.val.args[3].ref.t
                end
            elseif binding.val.args[2].kind === CSTParser.Tokens.DECLARATION
                if binding.val.args[3].typ === IDENTIFIER && binding.val.args[3].ref isa CSTParser.Binding
                    binding.t = binding.val.args[3]
                end
            end
        end
    end
end