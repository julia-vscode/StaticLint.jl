# function resolve_ref(r::Reference{CSTParser.IDENTIFIER}, bindings, res = Tuple{Reference,Any}[], unres = Reference[])
#     out = []
#     name = CSTParser.str_value(r.val)
#     if haskey(bindings, name)
#         for i = length(bindings[name]):-1:1
#             b = bindings[name][i]
#             if comp(r.index, r.pos, b.index, b.pos)
#                 push!(out, b)
#             elseif r.delayed
#                 for m in bindings["module"]
#                     if length(m.index) <= length(r.index) && m.index == r.index[1:length(m.index)] && b.index == m.index
#                         push!(out, b)
#                     end
#                 end
#             end
#         end
#     end
    
#     for m in bindings["using"]
#         if Symbol(name) in m.val.exported
#             push!(out, m.val.loaded[name].val)
#         end
#     end
#     if isempty(out) 
#         push!(unres, r)
#     else
#         push!(res, (r, first(out)))
#     end
#     return res, unres
# end

# function resolve_ref(r::Reference{CSTParser.BinarySyntaxOpCall}, bindings, res = Tuple{Reference,Any}[], unres = Reference[])
#     args = flatten_dot(r.val)
#     for a in args
#         if !(a isa CSTParser.IDENTIFIER)
#             return
#         end
#     end
#     offset = 0
#     res1 = []
#     for arg in args
#     end
#     return res, unres
# end

# function resolve_ref(r::Reference{CSTParser.EXPR{CSTParser.MacroName}}, bindings, res = Tuple{Reference,Any}[], unres = Reference[])
#     name = CSTParser.str_value(r.val.args[2])
#     if haskey(bindings, name)
#         for i = length(bindings[name]):-1:1
#             b = bindings[name][i]
#             if comp(r.index, r.pos, b.index, b.pos) && CSTParser.defines_macro(b.val)
#                 push!(res, (r, b))
#                 return res, unres            
#             end
#         end
#     end
#     mname = string("@", name)
#     for m in bindings["using"]
#         if Symbol(mname) in m.val.exported
#             push!(res, (r, m.val.loaded[mname].val))
#             return res, unres
#         end
#     end
#     push!(unres, r)
#     return res, unres
# end

function resolve_ref(r::Reference{CSTParser.IDENTIFIER}, bindings)
    out = []
    name = CSTParser.str_value(r.val)
    if haskey(bindings, name)
        for i = length(bindings[name]):-1:1
            b = bindings[name][i]
            if comp(r.index, r.pos, b.index, b.pos)
                push!(out, b)
            elseif r.delayed
                for m in bindings["module"]
                    if length(m.index) <= length(r.index) && m.index == r.index[1:length(m.index)] && b.index == m.index
                        push!(out, b)
                    end
                end
            end
        end
    end
    
    for m in bindings["using"]
        if Symbol(name) in m.val.exported
            push!(out, m.val.loaded[name].val)
        end
    end
    return isempty(out) ? r : (r, first(out))
end

function resolve_ref(r::Reference{CSTParser.BinarySyntaxOpCall}, bindings)
    args = flatten_dot(r.val)
    for a in args
        if !(a isa CSTParser.IDENTIFIER)
            return r
        end
    end
    offset = 0
    res1 = []
    for arg in args
    end
    return r
end

function resolve_ref(r::Reference{CSTParser.EXPR{CSTParser.MacroName}}, bindings)
    name = CSTParser.str_value(r.val.args[2])
    if haskey(bindings, name)
        for i = length(bindings[name]):-1:1
            b = bindings[name][i]
            if comp(r.index, r.pos, b.index, b.pos) && CSTParser.defines_macro(b.val)
                return (r, b)
            end
        end
    end
    mname = string("@", name)
    smname = Symbol(mname)
    for m in bindings["using"]
        if smname in m.val.exported
            return (r, m.val.loaded[mname].val)
        end
    end
    return r
end


function resolve_refs(refs, bindings, res = Tuple{Reference,Any}[], unres = Reference[])
    for r in refs
        rr = resolve_ref(r, bindings)
        if rr isa Reference
            push!(unres, rr)
        else
            push!(res, rr)
        end
    end
    return res, unres
end


function find_bindings_before(offset, state)
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


function get_ref(x, state, s, index, blockref, delayed)
    if blockref
        if x isa CSTParser.UnarySyntaxOpCall && x.arg1 isa CSTParser.OPERATOR && x.arg1.kind == CSTParser.Tokens.EX_OR
            return false
        else
            return true
        end
    else
        if x isa CSTParser.IDENTIFIER && !(x.val in ("new", "end", "ccall"))
            push!(state.refs, Reference(x, Location(state.loc.file, state.loc.offset), index, s.bindings, delayed))
            return false
        elseif x isa CSTParser.EXPR{CSTParser.MacroName}
            push!(state.refs, Reference(x, Location(state.loc.file, state.loc.offset), index, s.bindings, delayed))
            return true
        elseif x isa CSTParser.BinarySyntaxOpCall && x.op.kind == CSTParser.Tokens.DOT
            push!(state.refs, Reference(x, Location(state.loc.file, state.loc.offset), index, s.bindings, delayed))
            return true
        elseif x isa CSTParser.EXPR{CSTParser.Quote} || x isa CSTParser.EXPR{CSTParser.Quotenode} || x isa CSTParser.EXPR{CSTParser.x_Str}  || x isa CSTParser.EXPR{CSTParser.x_Cmd}
            return true
        
        end
    end
    return false
end

function cat_references(server, file, refs = [])
    append!(refs, file.state.refs)
    
    for incl in file.state.includes
        cat_references(server, incl.val, refs)
    end
    return refs
end