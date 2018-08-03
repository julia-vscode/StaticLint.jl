function get_ref(x, state::State, s::Scope, blockref, delayed)
    if blockref
        if x isa CSTParser.UnarySyntaxOpCall && x.arg1 isa CSTParser.OPERATOR && x.arg1.kind == CSTParser.Tokens.EX_OR
            return false
        else
            return true
        end
    else
        if x isa CSTParser.IDENTIFIER && !(x.val in ("new", "end", "ccall"))
            push!(state.refs, Reference(x, Location(state), SIndex(s.index, s.bindings), delayed))
            return false
        elseif x isa CSTParser.EXPR{CSTParser.MacroName}
            push!(state.refs, Reference(x, Location(state), SIndex(s.index, s.bindings), delayed))
            return true
        elseif x isa CSTParser.BinarySyntaxOpCall && x.op.kind == CSTParser.Tokens.DOT
            if x.arg2 isa CSTParser.EXPR{CSTParser.TupleH}
                push!(state.refs, Reference(x.arg1, Location(state), SIndex(s.index, s.bindings), delayed))
                return false
            else
                push!(state.refs, Reference(x, Location(state), SIndex(s.index, s.bindings), delayed))
                return true
            end
        elseif x isa CSTParser.EXPR{CSTParser.Quote} || x isa CSTParser.EXPR{CSTParser.Quotenode} || x isa CSTParser.EXPR{CSTParser.x_Str}  || x isa CSTParser.EXPR{CSTParser.x_Cmd}
            return true
        end
    end
    return false
end

function resolve_ref(r::Reference{CSTParser.IDENTIFIER}, bindings, rrefs)
    out = Any[]
    name = CSTParser.str_value(r.val)
    if haskey(bindings, name)
        for i = length(bindings[name]):-1:1
            b = bindings[name][i]
            if inscope(r.si, b.si) #inscope(r.index, r.pos, b.index, b.pos)
                push!(out, b)
            elseif r.delayed
                for m in bindings["module"]
                    if in_delayedscope(r.si.i, m.si.i, b.si.i)#in_delayedscope(r.index, m.index, b.index)
                        push!(out, b)
                    end
                end
            end
        end
    end
    if haskey(bindings[".used modules"], name)
        push!(out, bindings[".used modules"][name])
    else
        for (n, m) in bindings[".used modules"]
            if name in m.val[".exported"] && haskey(m.val, name)
                push!(out, ImportBinding(m.loc, m.si, m.val[name]))
            end
        end
    end
    
    if isempty(out)
        return r
    else
        ret = first(out)
        for i = 2:length(out)
            if lt(ret, out[i])
                ret = out[i]
            end
        end
        rr = ResolvedRef(r, ret)
        push!(rrefs, rr)
        return rr
    end
end



function resolve_ref(r::Reference{CSTParser.BinarySyntaxOpCall}, bindings, rrefs)
    # rhs 
    rr = Reference(r.val.arg2.args[1], Location(r.loc.file, r.loc.offset + r.val.arg1.fullspan + r.val.op.fullspan), r.si, r.delayed)
    # lhs
    lr = Reference(r.val.arg1, Location(r.loc.file, r.loc.offset), r.si, r.delayed)
    rlr = resolve_ref(lr, bindings, rrefs)
    if rlr isa ResolvedRef
        return resolve_ref(rr, bindings, rrefs, rlr)
    else
        return rlr
    end
end


resolve_ref(rr, bindings, rrefs) = rr
# Resolve reference given `lr.r`
function resolve_ref(rr::Reference, bindings, rrefs, rlr::ResolvedRef)
    if rlr.b.val isa ModuleBinding # root (rlr.b) is an imported module
        if Symbol(CSTParser.str_value(rr.val)) in rlr.b.val.internal
            b = rlr.b.val.loaded[CSTParser.str_value(rr.val)]
            rrr = ResolvedRef(rr, b)
            push!(rrefs, rrr)
            return rrr
        end
    elseif rlr.b.val isa Module && haskey(SymbolServer.server, string(rlr.b.val)) # root (rlr.b) is an imported module
        if Symbol(CSTParser.str_value(rr.val)) in SymbolServer.server[string(rlr.b.val)].internal
            b = SymbolServer.server[string(rlr.b.val)].loaded[CSTParser.str_value(rr.val)]
            rrr = ResolvedRef(rr, b)
            push!(rrefs, rrr)
            return rrr
        end
    end
    return rr
end 


function _hasfield(b::Binding, r::Reference)
    
end

function resolve_ref(r::Reference{CSTParser.EXPR{CSTParser.MacroName}}, bindings, refs)
    name = CSTParser.str_value(r.val.args[2])
    if haskey(bindings, name)
        for i = length(bindings[name]):-1:1
            b = bindings[name][i]
            # if inscope(r.index, r.pos, b.index, b.pos) && CSTParser.defines_macro(b.val)
            if inscope(r.si, b.si) && CSTParser.defines_macro(b.val)
                rr = ResolvedRef(r, b)
                push!(refs, rr)
                return rr
            end
        end
    end
    mname = string("@", name)
    smname = Symbol(mname)
    # for m in bindings["using"]
    #     if smname in m.val.exported
    #         rr = ResolvedRef(r, m.val.loaded[mname])
    #         push!(refs, rr)
    #         return rr
    #     end
    # end
    return r
end


function resolve_refs(refs, bindings, res = ResolvedRef[], unres = Reference[])
    for r in refs
        rr = resolve_ref(r, bindings, res)
        if rr == r
            push!(unres, rr)
        end
    end
    return res, unres
end


function find_bindings_before(offset, state::State)
    list = Dict()
    for (name, bindings) in state.bindings
        for b in bindings
            if b[1] < offset
                list[name] = b
            end
        end
    end
    return list
end




function cat_references(server, file, refs = [])
    append!(refs, file.state.refs)
    
    for incl in file.state.includes
        cat_references(server, incl.val, refs)
    end
    return refs
end

function get_methods(rref::ResolvedRef, bindings)
    M  = Binding[rref.b]
    B = bindings[CSTParser.str_value(rref.r.val)]
    firstind = findfirst(b->b==rref.b, B)
    firstind = firstind == nothing ? 0 : 1
    for i = firstind-1:-1:1
        if lt(B[i], rref.b) 
            if B[i].t == CSTParser.FunctionDef
                push!(M, B[i])
            elseif B[i].t in (CSTParser.Struct, CSTParser.Mutable, CSTParser.Abstract, CSTParser.Primitive)
                pushfirst!(M, B[i])
                break
            end
        else
            break
        end
    end
    M
end