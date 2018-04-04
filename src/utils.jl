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
            push!(state.bindings["module"], Binding(Location(state.loc.file, state.loc.offset), index1, 0, x))
        end
        s1 = Scope(s, [], state.loc.offset + x.span, 0, t, index1)
        push!(s.children, s1)
        int_binding(x, state, s1, index1)
        return s1, index1
    else
        return s, index
    end
end

function comp(r1, r2, b1, b2)
    nr = length(r1)
    nb = length(b1)
    nr < nb && return false
    suc = true
    for i = 1:nb
        suc = b1[i] ≤ r1[i]
    end
    !suc && return false
    if nb == nr
        return r2 >= b2
    else
        return r1[nb+1] >= b2
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
        b = Binding(Location(state.loc.file, state.loc.offset), index, s.bindings, SymbolServer.server[full])
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
            val = Binding(Location(state.loc.file, state.loc.offset), index, s.bindings, SymbolServer.server[rootmod].loaded[name])
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
        path = isloaded(state.server, path, state.loc.file)
        if !isempty(path)
            incl_f = getfile(state.server, path)
            if incl_f.scope.index != index
                cst = CST(incl_f)
                incl_f.state = State(Location(path, 0), Dict(), Reference[], [], state.server)
                incl_f.state.bindings["using"] = [Binding(Location("", 0), index, 0, SymbolServer.server["Base"]), Binding(Location("", 0), index, 0, SymbolServer.server["Core"])]
                incl_f.state.bindings["module"] = Binding[]
                incl_f.scope = Scope(nothing, Scope[], cst.span, s.bindings + 1, CSTParser.TopLevel, index)
                pass(cst, incl_f.state, incl_f.scope, index, false, false)
            end
            # push!(state.includes, Include(path, state.loc.offset, index, s.bindings))
            push!(state.includes, Include(incl_f, path, state.loc.offset, index, s.bindings))
            s.bindings = incl_f.scope.bindings
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


function get_stack(x, offset, pos = 0, stack = [])
    push!(stack, x)
    for a in x
        if pos < offset <= pos + a.fullspan
            return get_stack(a, offset, pos, stack)
        else
            pos += a.fullspan
        end
    end
    return stack
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