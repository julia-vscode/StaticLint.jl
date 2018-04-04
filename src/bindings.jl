function add_binding(name, x, state, s, index)
    s.bindings += 1
    val = Binding(Location(state.loc.file, state.loc.offset), index, s.bindings, x)
    add_binding(name, val, state)
end

function add_binding(name, binding, state)
    if haskey(state.bindings, name)
        push!(state.bindings[name], binding)
    else
        state.bindings[name] = Any[binding]
    end
end

function ext_binding(x, state, s, index)
    if CSTParser.defines_module(x) ||
        CSTParser.defines_function(x) ||
        CSTParser.defines_macro(x) ||
        CSTParser.defines_datatype(x)
        name = CSTParser.str_value(CSTParser.get_name(x))
        add_binding(name, x, state, s, index)
    elseif CSTParser.is_assignment(x)
        ass = x.arg1
        ass = CSTParser.rem_decl(ass)
        ass = CSTParser.rem_curly(ass)
        if ass isa CSTParser.IDENTIFIER
            name = CSTParser.str_value(ass)
            add_binding(name, x, state, s, index)
        elseif ass isa CSTParser.EXPR{CSTParser.TupleH}
            for a in CSTParser.flatten_tuple(ass)
                name = CSTParser.str_value(a)
                add_binding(name, x, state, s, index)
            end
        end
    elseif x isa CSTParser.EXPR{T} where T <: Union{CSTParser.Using,CSTParser.Import,CSTParser.ImportAll}
        get_imports(x, state, s, index)
    elseif x isa CSTParser.EXPR{CSTParser.MacroCall} && x.args[1] isa CSTParser.EXPR{CSTParser.MacroName} && length(x.args[1].args) > 1 &&  CSTParser.str_value(x.args[1].args[2]) == "enum"
        if length(x.args) > 3 && x.args[3] isa CSTParser.IDENTIFIER
            add_binding(CSTParser.str_value(x.args[3]), x, state, s, index)
        end
        for i = 4:length(x.args)
            if x.args[i] isa CSTParser.IDENTIFIER
                name = CSTParser.str_value(x.args[i])
                add_binding(name, x, state, s, index)
            end
        end
    end
end

function int_binding(x, state, s, index)
    if CSTParser.defines_module(x)
        name = CSTParser.str_value(CSTParser.get_name(x))
        add_binding(name, x, state, s, index)
    elseif CSTParser.defines_function(x)
        sig = CSTParser.get_sig(x)
        for param in CSTParser.get_sig_params(sig)
            add_binding(param, x, state, s, index)
        end
        for arg in CSTParser.get_args(x)
            name = CSTParser.str_value(arg)
            add_binding(name, x, state, s, index)
        end
    elseif CSTParser.defines_macro(x)
        for arg in CSTParser.get_args(x)
            name = CSTParser.str_value(arg)
            add_binding(name, x, state, s, index)
        end
    elseif CSTParser.defines_datatype(x)
        if x isa CSTParser.EXPR{CSTParser.Struct} || x isa CSTParser.EXPR{CSTParser.Mutable}
            isstruct = x isa CSTParser.EXPR{CSTParser.Struct}

            sig = CSTParser.get_sig(x)
            sig = CSTParser.rem_subtype(sig)
            sig = CSTParser.rem_where(sig)
            for arg in CSTParser.get_curly_params(sig)
                add_binding(arg, x, state, s, index)
            end
            for arg in x.args[isstruct ? 3 : 4]
                if !CSTParser.defines_function(arg)
                    name = CSTParser.str_value(CSTParser.rem_decl(arg))
                    add_binding(name, x, state, s, index)
                end
            end
        end
    elseif x isa CSTParser.EXPR{CSTParser.For}
        if is_for_iter(x.args[2]) && x.args[2].op.kind in (CSTParser.Tokens.IN, CSTParser.Tokens.ELEMENT_OF, CSTParser.Tokens.EQ)
            for a in CSTParser.flatten_tuple(x.args[2].arg1)
                add_binding(CSTParser.str_value(a), x, state, s, index)
            end
        else
            for i = 1:length(x.args[2].args)
                if is_for_iter(x.args[2].args[i]) && x.args[2].args[i].op.kind in (CSTParser.Tokens.IN, CSTParser.Tokens.ELEMENT_OF)
                    for a in CSTParser.flatten_tuple(x.args[2].args[i].arg1)
                        add_binding(CSTParser.str_value(a), x, state, s, index)
                    end
                end
            end
        end
    elseif x isa CSTParser.EXPR{CSTParser.Do}
        for arg in CSTParser.flatten_tuple(x.args[3])
            name = CSTParser.str_value(arg)
            add_binding(name, x, state, s, index)
        end
    elseif x isa CSTParser.EXPR{CSTParser.Generator}
        if is_for_iter(x.args[3]) && x.args[3].op.kind in (CSTParser.Tokens.IN, CSTParser.Tokens.ELEMENT_OF, CSTParser.Tokens.EQ)
            for i = 3:length(x.args)
                !is_for_iter(x.args[i]) && continue
                name = CSTParser.str_value(CSTParser.get_name(x.args[i].arg1))
                add_binding(name, x, state, s, index)
            end
        elseif x.args[3] isa CSTParser.EXPR{CSTParser.Filter}
            for i = 1:length(x.args[3].args)
                !is_for_iter(x.args[3].args[i]) && continue
                name = CSTParser.str_value(CSTParser.get_name(x.args[3].args[i].arg1))
                add_binding(name, x, state, s, index)
            end
        end
    elseif CSTParser.defines_anon_function(x)
        for arg in CSTParser.flatten_tuple(x.arg1)
            name = CSTParser.str_value(arg)
            add_binding(name, x, state, s, index)
        end
    end
end

function is_for_iter(x)
    x isa CSTParser.BinarySyntaxOpCall || x isa CSTParser.BinaryOpCall
end

function cat_bindings(server, file, bindings = Dict{String,Vector{Binding}}())
    for (k,v) in file.state.bindings
        if haskey(bindings, k)
            for b in v
                append!(bindings[k], v)
            end
        else
            bindings[k] = v
        end
    end
    
    for incl in file.state.includes
        cat_bindings(server, incl.val, bindings)
    end
    return bindings
end