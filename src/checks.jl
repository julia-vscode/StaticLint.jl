function check_call(x)
    if x.typ === Call
        name = CSTParser.get_name(x)
        if hasref(name)
            check_call(x, name.ref)
        end
    end
end

function check_call(x, b)
    fsig = CSTParser.rem_where_decl(CSTParser.get_sig(b.val))
    xn = length(x.args)
    fn = length(fsig.args)
    
    for i = 2:xn
    end
    if b.overwrites !== nothing && CSTParser.defines_function(b.overwrites.val)
        check_call(x, b.overwrites)
    end
end

function _typeof(x, state)
    if x.typ in (CSTParser.Abstract, CSTParser.Primitive, CSTParser.Struct, CSTParser.Mutable)
        return getsymbolserver(state.server)["Core"].vals["DataType"]
    elseif x.typ in (CSTParser.ModuleH, CSTParser.BareModule)
        return getsymbolserver(state.server)["Core"].vals["Module"]
    elseif x.typ in (CSTParser.ModuleH, CSTParser.BareModule)
        return getsymbolserver["Core"].vals["Module"]
    elseif CSTParser.defines_function(x)
        return return getsymbolserver(state.server)["Core"].vals["Function"]
    end
end
