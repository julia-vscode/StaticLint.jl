function infer(b, server, rrefs)

    if b.t isa Binding || b.t isa SymbolServer.SymStore
        # type already known
        return 
    elseif b.val isa CSTParser.BinarySyntaxOpCall && b.val.op.kind == CSTParser.Tokenize.Tokens.EQ # assignment
        if b.val.arg2 isa CSTParser.LITERAL
            # rhs is a literal, inference is trivial
            if b.val.arg2.kind == CSTParser.Tokenize.Tokens.STRING || b.val.arg2.kind == CSTParser.Tokenize.Tokens.TRIPLE_STRING
                b.t = server.packages["Core"].vals["String"]
            elseif b.val.arg2.kind == CSTParser.Tokenize.Tokens.INTEGER
                b.t = server.packages["Core"].vals["Int"]
            elseif b.val.arg2.kind == CSTParser.Tokenize.Tokens.FLOAT
                b.t = server.packages["Core"].vals["Float64"]
            elseif b.val.arg2.kind == CSTParser.Tokenize.Tokens.HEX_INT || b.val.arg2.kind == CSTParser.Tokenize.Tokens.OCT_INT || b.val.arg2.kind == CSTParser.Tokenize.Tokens.BIN_INT
                b.t = server.packages["Core"].vals["UInt64"]
            elseif b.val.arg2.kind == CSTParser.Tokenize.Tokens.CHAR
                b.t = server.packages["Core"].vals["Char"]
            end
        elseif b.val.arg2 isa CSTParser.IDENTIFIER
            # rhs is an ID, copy typing from that reference
            offset = b.loc.offset + b.val.arg1.fullspan + b.val.op.fullspan
            rhs_ref = find_ref(rrefs, offset, b.loc.file)
            if rhs_ref.b isa ImportBinding
                b.t = rhs_ref.b.val
            elseif rhs_ref != nothing
                if rhs_ref.b.t == nothing
                    infer(rhs_ref.b, server, rrefs)
                end
                b.t = rhs_ref.b.t
            end
        elseif b.val.arg2 isa CSTParser.EXPR{CSTParser.Ref}
        elseif b.val.arg2 isa CSTParser.EXPR{CSTParser.Call}
            offset = b.loc.offset + b.val.arg1.fullspan + b.val.op.fullspan
            rhs_ref = find_ref(rrefs, offset, b.loc.file)
            if rhs_ref.b isa ImportBinding
                if rhs_ref.b.val isa SymbolServer.structStore || rhs_ref.b.val isa SymbolServer.abstractStore || rhs_ref.b.val isa SymbolServer.primitiveStore
                    b.t = rhs_ref.b.val
                end
            elseif rhs_ref.b.t == server.packages["Core"].vals["DataType"]
                b.t = rhs_ref.b
            end
        end
    end
end