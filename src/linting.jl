@enum(LintCode, IncludeFail)
const LintMessages = Dict{LintCode,String}(
    IncludeFail => "Cannot include file."
    )

struct LintError
    code::LintCode
    loc::Location
    val::CSTParser.AbstractEXPR
end

function infer_literal(x::CSTParser.LITERAL, server)
    if x.kind == CSTParser.Tokenize.Tokens.STRING || x.kind == CSTParser.Tokenize.Tokens.TRIPLE_STRING
        return server.packages["Core"].vals["String"]
    elseif x.kind == CSTParser.Tokenize.Tokens.INTEGER
        return server.packages["Core"].vals["Int"]
    elseif x.kind == CSTParser.Tokenize.Tokens.FLOAT
        return server.packages["Core"].vals["Float64"]
    elseif x.kind == CSTParser.Tokenize.Tokens.HEX_INT || x.kind == CSTParser.Tokenize.Tokens.OCT_INT || x.kind == CSTParser.Tokenize.Tokens.BIN_INT
        return server.packages["Core"].vals["UInt64"]
    elseif x.kind == CSTParser.Tokenize.Tokens.CHAR
        return server.packages["Core"].vals["Char"]
    end
end


function infer(b, server, rrefs)
    if b.t isa Binding || b.t isa SymbolServer.SymStore
        # type already known
        return 
    elseif b.val isa CSTParser.BinarySyntaxOpCall && b.val.op.kind == CSTParser.Tokenize.Tokens.EQ # assignment
        if b.val.arg2 isa CSTParser.LITERAL
            # rhs is a literal, inference is trivial
            b.t = infer_literal(b.val.arg2, server)
        elseif b.val.arg2 isa CSTParser.IDENTIFIER
            # rhs is an ID, copy typing from that reference
            offset = b.loc.offset + b.val.arg1.fullspan + b.val.op.fullspan
            rhs_ref = find_ref(rrefs, offset, b.loc.file)
            if rhs_ref == nothing
            elseif rhs_ref.b isa ImportBinding
                b.t = rhs_ref.b.val
            else
                if rhs_ref.b.t == nothing
                    infer(rhs_ref.b, server, rrefs)
                end
                b.t = rhs_ref.b.t
            end
        elseif b.val.arg2 isa CSTParser.EXPR{CSTParser.Ref}
        elseif b.val.arg2 isa CSTParser.EXPR{CSTParser.Call}
            offset = b.loc.offset + b.val.arg1.fullspan + b.val.op.fullspan
            rhs_ref = find_ref(rrefs, offset, b.loc.file)
            if rhs_ref == nothing
            elseif rhs_ref.b isa ImportBinding
                if rhs_ref.b.val isa SymbolServer.structStore || rhs_ref.b.val isa SymbolServer.abstractStore || rhs_ref.b.val isa SymbolServer.primitiveStore
                    b.t = rhs_ref.b.val
                end
            elseif rhs_ref.b.t == server.packages["Core"].vals["DataType"]
                b.t = rhs_ref.b
            end
        end
    end
end

