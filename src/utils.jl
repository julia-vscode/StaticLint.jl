function create_scope(x, state, s)
    def_f = CSTParser.defines_function(x)
    if CSTParser.defines_module(x) ||
        def_f ||
        CSTParser.defines_macro(x) ||
        CSTParser.defines_datatype(x) ||
        x isa CSTParser.EXPR{CSTParser.Let} ||
        x isa CSTParser.EXPR{CSTParser.Do} ||
        x isa CSTParser.EXPR{CSTParser.While} ||
        x isa CSTParser.EXPR{CSTParser.For} ||
        x isa CSTParser.EXPR{CSTParser.Try} ||
        x isa CSTParser.EXPR{CSTParser.Generator} ||
        x isa CSTParser.WhereOpCall ||
        CSTParser.defines_anon_function(x) ||
        (x isa CSTParser.BinarySyntaxOpCall && x.op.kind == CSTParser.Tokens.EQ && x.arg1 isa CSTParser.EXPR{CSTParser.Curly})
        if def_f
            t = CSTParser.FunctionDef
        else
            t = typeof(x)
            if x isa CSTParser.EXPR
                t = t.parameters[1]
            end
        end
        s.bindings += 1
        index1 = cattuple(s.index,s.bindings)
        if CSTParser.defines_module(x) # add module barrier
            add_module_barrier(state, index1, x)
        end
        s1 = Scope(s, Scope[], state.loc.offset .+ x.span, t, index1, 0)
        push!(s.children, s1)
        int_binding(x, state, s1)
        return s1
    elseif x isa CSTParser.EXPR{CSTParser.Using} || 
        x isa CSTParser.EXPR{CSTParser.Import} || 
        x isa CSTParser.EXPR{CSTParser.ImportAll}
        t = typeof(x).parameters[1]
        s.bindings += 1
        index1 = cattuple(s.index,s.bindings)
        s1 = Scope(s, Scope[], state.loc.offset .+ x.span, t, index1, 0)
        push!(s.children, s1)
        get_imports(x, state, s1)
        return s1
    else
        return s
    end
end

function add_module_barrier(state, index, x)
    push!(state.modules.list, Binding(Location(state), SIndex(index, 0), x, nothing))
    push!(state.modules.names, CSTParser.str_value(CSTParser.get_name(x)))
end

inscope(asi, bsi) = inscope(asi.i, asi.n, bsi.i, bsi.n)
@generated function inscope(rind::NTuple{rN,Int}, rpos::Int, bind::NTuple{bN,Int}, bpos::Int) where {bN,rN}
    if bN > rN
        return :(false)
    elseif bN == rN
        return :(rind == bind && rpos >= bpos)
    else
        return quote
            i = 1
            while i <= $(bN)
                rind[i] != bind[i] && return false
                i += 1
            end
            return rind[i] ≥ bpos
        end
    end
end

function lt(ai::NTuple{na,Int},ap, bi::NTuple{nb,Int}, bp) where {na, nb}
    if na == nb
        for i = 1:na
            if ai[i] > bi[i]
                return false
            end
        end
        return ap < bp
    elseif na > nb
        for i = 1:nb
            if ai[i] > bi[i]
                return false
            end
        end
        return ai[nb + 1] < bp
    else
        for i = 1:na
            if ai[i] > bi[i]
                return false
            end
        end
        return ap < bi[na + 1]
    end 
end


# lt(a, b) = lt(a.si.i, a.si.n, b.si.i, b.si.n)
lt(a,b) = lt(a.si, b.si)
lt(a::SIndex, b::SIndex) = lt(a.i, a.n, b.i, b.n)

@generated function in_delayedscope(rindex::NTuple{Nr,Int}, mindex::NTuple{Nm,Int}, bindex::NTuple{Nb,Int}) where {Nr,Nm,Nb}
    out = :()
    if bindex != mindex || Nm > Nr || Nb > Nr
        return :(false)
    elseif Nm == Nb == 0
        return true
    else
        out = :(rindex[$Nm] == mindex[$Nm])
        for i = Nm-1:-1:1
            out = :(rindex[$i] == mindex[$i] && $out)
        end
        return Expr(:&&,:(bindex == mindex), out)
    end
end

function cattuple(v::Tuple, i)
    n = length(v)    
    ntuple(j-> j<=n ? v[j] : i, n + 1)
end
function cattuple(v1::Tuple, v2::Tuple)
    n1 = length(v1)
    n2 = length(v2)
    ntuple(j -> j <= n1 ? v1[j] : v2[j-n1], n1 + n2)
end

@generated function shrink_tuple(t::NTuple{N,Int}) where N
    out = :()
    for i = 1:N-1
        push!(out.args, :(t[$i]))
    end     
    return out
end

@generated function add_to_tuple(t::NTuple{N,Int}, n) where N
    out = :()
    for i = 1:N
        push!(out.args, :(t[$i]))
    end
    push!(out.args, :n)
    return out
end


shrink_sindex(si::SIndex) = SIndex(shrink_tuple(si.i), si.i[end])
function shrink_sindex(si::SIndex, n) 
    i = 0
    while i < n
        si = shrink_sindex(si)
        i+=1
    end
    si
end

function get_path(x::CSTParser.EXPR{CSTParser.Call})
    if length(x.args) == 4
        parg = x.args[3]
        if CSTParser.is_lit_string(parg)
            path = CSTParser.str_value(parg)
            return path
        elseif parg isa CSTParser.EXPR{CSTParser.Call} && parg.args[1] isa CSTParser.IDENTIFIER && CSTParser.str_value(parg.args[1]) == "joinpath"
            path = ""
            for i = 2:length(parg.args)
                arg = parg.args[i]
                if arg isa CSTParser.PUNCTUATION
                elseif CSTParser.is_lit_string(arg)
                    path = string(path, "/", CSTParser.str_value(arg))
                else
                    return ""
                end
            end
            return path
        end
    end
    return ""
end

function get_include(x, state, s)
    if x isa CSTParser.EXPR{CSTParser.Call} && CSTParser.str_value(x.args[1]) == "include"
        path = get_path(x)
        if is_loaded(state.server, path)
            file = getfile(state.server, path)
            loaded = true
        elseif is_loaded(state.server, joinpath(dirname(state.loc.file), path))
            loaded = true
            path = joinpath(dirname(state.loc.file), path)
            file = getfile(state.server, path)
        elseif can_load(state.server, path)
            loaded = true
            file = load_file(state.server, path, s.index, s.bindings, state.loc.file)
        elseif can_load(state.server, joinpath(dirname(state.loc.file), path))
            loaded = true
            path = joinpath(dirname(state.loc.file), path)
            file = load_file(state.server, path, s.index, s.bindings, state.loc.file)
        else
            loaded = false
        end
        if loaded
            if !(file.index == s.index && file.nb == s.bindings)
                file.index = s.index
                file.nb = s.bindings
                StaticLint.pass(file)
            end
            push!(state.includes, Include(file, path, state.loc.offset, s.index, s.bindings))
            s.bindings = file.scope.bindings
        else
            push!(state.linterrors, LintError(IncludeFail, deepcopy(state.loc), x))
        end
    end
end



function get_stack(x, offset, pos = 0, stack = [], offsets = Int[])
    push!(stack, x)
    push!(offsets, pos)
    for a in x
        if pos <= offset < pos + a.fullspan
            return get_stack(a, offset, pos, stack, offsets)
        else
            pos += a.fullspan
        end
    end
    return stack, offsets
end



Location(state::State) = Location(state.loc.file, state.loc.offset)
