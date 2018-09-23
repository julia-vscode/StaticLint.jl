function get_ref(x, state::State, s::Scope, blockref, delayed)
    if blockref
        if x isa CSTParser.UnarySyntaxOpCall && x.arg1 isa CSTParser.OPERATOR && x.arg1.kind == CSTParser.Tokens.EX_OR
            # Sets `blockref` to false, if we're in a string, etc. we're now interpolating.
            return false
        else
            return true
        end
    else
        if x isa CSTParser.IDENTIFIER && !(x.val in ("new", "end", "ccall"))
            # Add symbol reference (ignore some keywords)
            push!(state.refs, Reference(x, Location(state), SIndex(s.index, s.bindings), delayed))
            return false
        elseif x isa CSTParser.EXPR{CSTParser.MacroName}
            # Add macroname reference
            push!(state.refs, Reference(x, Location(state), SIndex(s.index, s.bindings), delayed))
            return true
        elseif x isa CSTParser.BinarySyntaxOpCall && x.op.kind == CSTParser.Tokens.DOT
            if x.arg2 isa CSTParser.EXPR{CSTParser.TupleH}
                # Add function call (broadcasted) name reference.
                push!(state.refs, Reference(x.arg1, Location(state), SIndex(s.index, s.bindings), delayed))
                return false
            elseif x.arg2 isa CSTParser.EXPR{CSTParser.Quotenode}
                # Add dot-access reference.
                push!(state.refs, Reference(x, Location(state), SIndex(s.index, s.bindings), delayed))
                return true
            end
        elseif x isa CSTParser.EXPR{CSTParser.Quote} || x isa CSTParser.EXPR{CSTParser.Quotenode} || x isa CSTParser.EXPR{CSTParser.x_Str}  || x isa CSTParser.EXPR{CSTParser.x_Cmd}
            # Set `blockref` to true, we're in a quote, string or command
            return true
        end
    end
    return false
end

function res_ref(name, ind, bindings)
    if haskey(bindings, ind) && haskey(bindings[ind], name)
        return bindings[ind][name]
    elseif length(ind) > 0
        return res_ref(name, shrink_tuple(ind), bindings)
    else
        return []
    end
end

function resolve_ref(r::Reference{T}, state::State, rrefs) where T <: Union{CSTParser.IDENTIFIER,CSTParser.EXPR{CSTParser.MacroName}}
    out = Any[]
    name = CSTParser.str_value(r.val)
    ind = r.si.i
    append!(out,res_ref(name, ind, state.bindings))
    # if haskey(state.bindings, name)
    #     for i = length(state.bindings[name]):-1:1
    #         b = state.bindings[name][i]
    #         if inscope(r.si, b.si) #inscope(r.index, r.pos, b.index, b.pos)
    #             push!(out, b)
    #         elseif r.delayed
    #             for m in state.modules
    #                 if in_delayedscope(r.si.i, m.si.i, b.si.i) # lots of action here 
    #                     push!(out, b)
    #                 end
    #             end
    #         end
    #     end
    # end
    if haskey(state.used_modules, name)
        push!(out, state.used_modules[name])
    else
        for m in state.used_modules
            if name in m[2].val[".exported"] && haskey(m[2].val, name) # lots of action here
                push!(out, ImportBinding(m[2].loc, m[2].si, m[2].val[name]))
            end
        end
    end
    
    #get lower bound on scope
    lbsi = SIndex((), 0)
    for m in state.modules
        if inscope(r.si, m.si) && lt(lbsi, m.si)
            lbsi = m.si
        end
    end

    if isempty(out)
        return r
    else
        ret = first(out)
        for i = 2:length(out)
            if r.delayed && length(r.si.i) > length(out[i].si.i) && in_delayedscope(r.si.i, lbsi.i, out[i].si.i) && lt(ret, out[i])

                ret = out[i]
            elseif lt(ret, out[i]) && inscope(r.si, out[i].si)
                ret = out[i]
            end
        end
        rr = ResolvedRef(r, ret)
        push!(rrefs, rr)
        push!(ret.refs, r)
        return rr
        # return out
    end
end



function resolve_ref(r::Reference{CSTParser.BinarySyntaxOpCall}, state, rrefs)
    (length(r.val.arg2.args) == 0 || !(r.val.arg2 isa CSTParser.EXPR{CSTParser.Quotenode})) && return r
    # rhs 
    rr = Reference(r.val.arg2.args[1], Location(r.loc.file, r.loc.offset + r.val.arg1.fullspan + r.val.op.fullspan), r.si, r.delayed)
    # lhs
    lr = Reference(r.val.arg1, Location(r.loc.file, r.loc.offset), r.si, r.delayed)
    rlr = resolve_ref(lr, state, rrefs)
    if rlr isa ResolvedRef
        return resolve_ref(rr, state, rrefs, rlr)
    else
        return rlr
    end
end


resolve_ref(rr, bindings, rrefs) = rr
# Resolve reference given `lr.r`
function resolve_ref(rr::Reference, state, rrefs, rlr::ResolvedRef)
    if rlr.b.val isa Dict # root (rlr.b) is an imported module
        if haskey(rlr.b.val, CSTParser.str_value(rr.val))
            b = rlr.b.val[CSTParser.str_value(rr.val)]
            b = ImportBinding(rlr.b.loc, rlr.b.si, rlr.b.val[CSTParser.str_value(rr.val)])
            rrr = ResolvedRef(rr, b)
            push!(rrefs, rrr)
            return rrr
        end
    end
    return rr
end 


function resolve_refs(refs, state, res = ResolvedRef[], unres = Reference[])
    for r in refs
        rr = resolve_ref(r, state, res)
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

function get_methods(rref::ResolvedRef, state)
    M  = Binding[rref.b]
    B = state.bindings[CSTParser.str_value(rref.r.val)]
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