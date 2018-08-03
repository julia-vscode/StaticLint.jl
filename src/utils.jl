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
        CSTParser.defines_anon_function(x)
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
            push!(state.bindings["module"], Binding(Location(state), SIndex(index1, 0), x, nothing))
        end
        s1 = Scope(s, Scope[], state.loc.offset .+ x.span, t, index1, 0)
        push!(s.children, s1)
        int_binding(x, state, s1)
        return s1
    else
        return s
    end
end


inscope(asi, bsi) = inscope(asi.i, asi.n, bsi.i, bsi.n)
function inscope(rind, rpos, bind, bpos)
    nrind = length(rind)
    nbind = length(bind)
    nbind > nrind && return false
    i = 1
    while i <= nbind
        rind[i] != bind[i] && return false
        i += 1
    end
    if nrind == nbind
        return rpos ≥ bpos
    else
        return rind[i] ≥ bpos
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

lt(a, b) = lt(a.si.i, a.si.n, b.si.i, b.si.n)

@generated function in_delayedscope(rindex::NTuple{Nr,Int}, mindex::NTuple{Nm,Int}, bindex::NTuple{Nb,Int}) where {Nr,Nm,Nb}
    out = :()
    if bindex != mindex || Nm > Nr || Nb > Nr
        return :(false)
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
        end
    end
end

function find_root(server, path)
    for (n,f) in server.files
        for incl in f.state.includes
            if path == incl.file
                return find_root(server, n)
            end
        end
    end
    return path
end


function get_stack(x, offset, pos = 0, stack = [], offsets = Int[])
    push!(stack, x)
    push!(offsets, pos)
    for a in x
        if pos < offset <= pos + a.fullspan
            return get_stack(a, offset, pos, stack, offsets)
        else
            pos += a.fullspan
        end
    end
    return stack, offsets
end

function flatten_dot(x::CSTParser.BinarySyntaxOpCall, stack = [])
    if x.arg1 isa CSTParser.BinarySyntaxOpCall
        flatten_dot(x.arg1, stack)
    else
        push!(stack, x.arg1)
    end
    push!(stack, x.arg2 isa CSTParser.EXPR{CSTParser.Quotenode} ? x.arg2.args[1] : x.arg2)
    return stack
end

Location(state::State) = Location(state.loc.file, state.loc.offset)