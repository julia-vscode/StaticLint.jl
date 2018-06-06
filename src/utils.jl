function create_scope(x, state, s, index)
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
        index1 = cattuple(index,s.bindings)
        if CSTParser.defines_module(x) # add module barrier
            push!(state.bindings["module"], Binding(Location(state.loc.file, state.loc.offset), index1, 0, x, nothing))
        end
        s1 = Scope(s, [], state.loc.offset + x.span, t, index1, 0, Set())
        push!(s.children, s1)
        int_binding(x, state, s1, index1)
        return s1, index1
    else
        return s, index
    end
end

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
lt(a::Binding, b::Binding) = lt(a.index, a.pos, b.index, b.pos)

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

function load_import(x, state, s, index, root, block, predots, u)
    full = string(root, join(block, "."))
    if isempty(root)
        firstmod = block[1]
    else
        firstmod = split(root, '.')[1]
    end
    rootmod = strip(string(root, join(view(block, 1:length(block)-1))), '.')
    if full in keys(SymbolServer.server)
        if !SymbolServer.server[full].is_loaded && !SymbolServer.server[full].load_failed
            SymbolServer.load_module(full)
            !SymbolServer.server[full].is_loaded && return
        end
        b = Binding(Location(state.loc.file, state.loc.offset), index, s.bindings, SymbolServer.server[full], nothing)
        name = last(block)
        add_binding(name, b, state)
        if u
            push!(state.bindings["using"], b)
        end
    elseif rootmod in keys(SymbolServer.server)
        if !SymbolServer.server[rootmod].is_loaded && !SymbolServer.server[rootmod].load_failed
            SymbolServer.load_module(rootmod)
            !SymbolServer.server[rootmod].is_loaded && return
        end
        name = last(block)
        if name in keys(SymbolServer.server[rootmod].loaded)
            s.bindings += 1
            val = Binding(Location(state.loc.file, state.loc.offset), index, s.bindings, SymbolServer.server[rootmod].loaded[name], nothing)
            add_binding(name, val, state)
        end
    else
    end
end

function get_imports(x, state, s, index)
    u = x isa CSTParser.EXPR{CSTParser.Using}
    i = 2
    predots = 0
    root = ""
    block = String[]
    while i ≤ length(x.args)
        arg = x.args[i]
        if arg isa CSTParser.PUNCTUATION && arg.kind == CSTParser.Tokens.DOT
            if isempty(block)
                predots += 1
            end
        elseif arg isa CSTParser.PUNCTUATION && arg.kind == CSTParser.Tokens.COMMA   
            load_import(x, state, s, index, root, block, predots, u)
            empty!(block)
        elseif arg isa CSTParser.OPERATOR && arg.kind == CSTParser.Tokens.COLON
            root = string(join(block, "."), ".")
            empty!(block)
        elseif arg isa CSTParser.IDENTIFIER
            push!(block, CSTParser.str_value(arg))
        else 
            return
        end
        i += 1
    end
    if !isempty(block)
        load_import(x, state, s, index, root, block, predots, u)
    end
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

function get_include(x, state, s, index)
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
            file = load_file(state.server, path, index, s.bindings, state.loc.file)
        elseif can_load(state.server, joinpath(dirname(state.loc.file), path))
            loaded = true
            path = joinpath(dirname(state.loc.file), path)
            file = load_file(state.server, path, index, s.bindings, state.loc.file)
        else
            loaded = false
        end
        if loaded
            push!(state.includes, Include(file, path, state.loc.offset, index, s.bindings))
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