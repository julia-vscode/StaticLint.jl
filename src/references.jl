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

function resolve_current_scope(r, state, name)
    ret = nothing
    if haskey(state.bindings, r.si.i) && haskey(state.bindings[r.si.i], name)
        for b in state.bindings[r.si.i][name]
            if ret == nothing
                if r.delayed
                    ret = b
                elseif inscope(r.si, b.si)
                    ret = b
                end
            elseif lt(ret.si, b.si)
                ret = b
            elseif inscope(r.si, b.si) && lt(ret.si, b.si)
                ret = b
            end
        end
    end
    return ret
end

function resolve_upper_scope(ret, r, state, name, lbsi) ret end
function resolve_upper_scope(ret::Nothing, r, state, name, lbsi)
    ind = r.si.i
    while length(ind) > 0 && length(ind) > length(lbsi.i) 
        n = last(ind)
        ind = shrink_tuple(ind)
        if haskey(state.bindings, ind) && haskey(state.bindings[ind], name)
            for b in state.bindings[ind][name]
                if ret == nothing
                    if r.delayed
                        ret = b
                    elseif b.si.n <= n
                        ret = b
                    end
                elseif lt(ret.si, b.si)
                    ret = b
                end
            end
        end
    end
    return ret
end

function resolve_import_scope(ret, state, name) ret end
function resolve_import_scope(ret::Nothing, state, name)
    for m in state.used_modules 
        if m.val.name == name
            return ImportBinding(m.loc, m.si, m.val)
        elseif name in m.val.exported && haskey(m.val.vals, name)
            if m.val.vals[name] isa String
                if haskey(state.server.packages, name)
                    #Package reexports another package
                    return ImportBinding(m.loc, m.si, state.server.packages[name])
                end
            else
                return ImportBinding(m.loc, m.si, m.val.vals[name])
            end
        end
    end
end

function resolve_ref(r::Reference{T}, state::State, rrefs, urefs) where T <: Union{CSTParser.IDENTIFIER,CSTParser.EXPR{CSTParser.MacroName}}
    name = CSTParser.str_value(r.val)
    lbsi = get_lbsi(r, state)
    ret = resolve_current_scope(r, state, name)
    ret = resolve_upper_scope(ret, r, state, name, lbsi)
    ret = resolve_import_scope(ret, state, name)

    if ret == nothing
        push!(urefs, r)
        return r
    else
        push!(ret.refs, r)
        rr = ResolvedRef(r, ret)
        push!(rrefs, rr)
        return rr
    end
end

function get_lbsi(ref::Reference, state::State)
    lbsi = SIndex((), 0)
    for m in state.modules.list
        if inscope(ref.si, m.si) && lt(lbsi, m.si)
            lbsi = m.si
        end
    end
    lbsi
end


function resolve_ref(r::Reference{CSTParser.BinarySyntaxOpCall}, state, rrefs, urefs)
    (length(r.val.arg2.args) == 0 || !(r.val.arg2 isa CSTParser.EXPR{CSTParser.Quotenode})) && return r
    # rhs 
    rr = Reference(r.val.arg2.args[1], Location(r.loc.file, r.loc.offset + r.val.arg1.fullspan + r.val.op.fullspan), r.si, r.delayed)
    # lhs
    lr = Reference(r.val.arg1, Location(r.loc.file, r.loc.offset), r.si, r.delayed)
    rlr = resolve_ref(lr, state, rrefs, urefs)
    if r.val.arg1 isa CSTParser.IDENTIFIER && rlr isa Reference
        push!(urefs, rlr)
    end
    if rlr isa ResolvedRef
        return resolve_dot_ref(rr, state, rrefs, rlr)
    else
        return rlr
    end
end


resolve_ref(rr, bindings, rrefs, urefs) = rr
# Resolve reference given `lr.r`
function resolve_dot_ref(rr::Reference, state, rrefs, rlr::ResolvedRef)
    if rlr.b.val isa SymbolServer.ModuleStore # root (rlr.b) is an imported module
        if haskey(rlr.b.val.vals, CSTParser.str_value(rr.val))
            b = rlr.b.val.vals[CSTParser.str_value(rr.val)]            
            if b isa String 
                if haskey(state.server.packages, b)# handles reference to dependency package
                    b = state.server.packages[b]
                else
                    return rr
                end
            end
            b = ImportBinding(rlr.b.loc, rlr.b.si, b)
            rrr = ResolvedRef(rr, b)
            push!(rrefs, rrr)
            return rrr
        end
    end
    return rr
end 


function resolve_refs(refs, state, rrefs = ResolvedRef[], urefs = Reference[])
    for r in refs
        rr = resolve_ref(r, state, rrefs, urefs)
    end
    return rrefs, urefs
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

function cat_references(file, refs = Reference[])
    append!(refs, file.state.refs)
    
    for incl in file.state.includes
        cat_references(incl.val, refs)
    end
    return refs
end

function get_methods(rref::ResolvedRef, state)
    M  = Binding[rref.b]
    if haskey(state.bindings, rref.b.si.i)
        if haskey(state.bindings[rref.b.si.i], CSTParser.str_value(rref.r.val))
            for b in state.bindings[rref.b.si.i][CSTParser.str_value(rref.r.val)]
                if CSTParser.defines_function(b.val)
                    push!(M, b)
                else
                    pushfirst!(M, b)
                    break
                end
            end
        end
    end
    # B = state.bindings[CSTParser.str_value(rref.r.val)]
    # firstind = findfirst(b->b==rref.b, B)
    # firstind = firstind == nothing ? 0 : 1
    # for i = firstind-1:-1:1
    #     if lt(B[i], rref.b) 
    #         if B[i].t == CSTParser.FunctionDef
    #             push!(M, B[i])
    #         elseif B[i].t in (CSTParser.Struct, CSTParser.Mutable, CSTParser.Abstract, CSTParser.Primitive)
    #             pushfirst!(M, B[i])
    #             break
    #         end
    #     else
    #         break
    #     end
    # end
    M
end