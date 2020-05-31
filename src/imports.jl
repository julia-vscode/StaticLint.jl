function resolve_import(x, state::State)
    if typof(x) === Using || typof(x) === Import
        u = typof(x) === Using
        i = 2
        n = length(x)

        root = par = getsymbolserver(state.server)
        while i <= n
            arg = x[i]
            if is_id_or_macroname(arg)
                if refof(arg) !== nothing
                    par = refof(arg)
                else
                    par = _get_field(par, arg, state)
                end
            elseif ispunctuation(arg) && kindof(arg) == CSTParser.Tokens.COMMA
                # end of chain, make available
                if i > 2
                    _mark_import_arg(x[i - 1], par, state, u)
                end
                par = root
            elseif isoperator(arg) && kindof(arg) == CSTParser.Tokens.COLON
                root = par
                if par !== nothing && i > 2 && isidentifier(x[i - 1]) && refof(x[i - 1]) === nothing
                    setref!(x[i - 1], par)
                end
            elseif ispunctuation(arg) && kindof(arg) == CSTParser.Tokens.DOT
                # dot between identifiers
                if par !== nothing && i > 2 && isidentifier(x[i - 1]) && refof(x[i - 1]) === nothing
                    setref!(x[i - 1], par)
                end
            elseif isoperator(arg) && kindof(arg) == CSTParser.Tokens.DOT
                # dot prexceding identifiser
                if par == root == getsymbolserver(state.server)
                    par = state.scope
                elseif par isa Scope && parentof(par) !== nothing
                    par = parentof(par)
                else
                    return
                end
            elseif !isoperator(arg)
                return
            end
            if i == n
                _mark_import_arg(x[i], par, state, u)
            end
            i += 1
        end
    end
end

function _mark_import_arg(arg, par, state, usinged)
    if par !== nothing && is_id_or_macroname(arg)
        if par isa Binding # mark reference to binding
            push!(par.refs, arg)
        end
        if par isa SymbolServer.VarRef
            par = SymbolServer._lookup(par, getsymbolserver(state.server), true)
            !(par isa SymbolServer.SymStore) && return
        end
        if bindingof(arg) === nothing
            if !hasmeta(arg)
                arg.meta = Meta()
            end
            arg.meta.binding = Binding(arg, par, _typeof(par, state), [], nothing, nothing)
        end

        if usinged
            if par isa SymbolServer.ModuleStore
                add_to_imported_modules(state.scope, Symbol(valofid(arg)), par)
            elseif par isa Binding && par.val isa SymbolServer.ModuleStore
                add_to_imported_modules(state.scope, Symbol(valofid(arg)), par.val)
            elseif par isa Binding && par.val isa EXPR && CSTParser.defines_module(par.val)
                add_to_imported_modules(state.scope, Symbol(valofid(arg)), scopeof(par.val))
            elseif par isa Binding && par.val isa Binding && par.val.val isa EXPR && CSTParser.defines_module(par.val.val)
                add_to_imported_modules(state.scope, Symbol(valofid(arg)), scopeof(par.val.val))
            end
        end
    end
end

function add_to_imported_modules(scope::Scope, name::Symbol, val)
    if scope.modules isa Dict
        scope.modules[name] = val
    else
        modules = Dict(name => val)
    end
end
no_modules_above(s::Scope) = !CSTParser.defines_module(s.expr) || s.parent === nothing || no_modules_above(s.parent)
function get_named_toplevel_module(s::Scope, name::String)
    if CSTParser.defines_module(s.expr) && valofid(CSTParser.get_name(s.expr)) == name && no_modules_above(s)
        return s.expr
    elseif s.parent isa Scope
        return get_named_toplevel_module(s.parent, name)
    end
    return nothing
end
function _get_field(par, arg, state)
    arg_str_rep = CSTParser.str_value(arg)
    if par isa SymbolServer.EnvStore
        if (arg_scope = retrieve_scope(arg)) !== nothing && (tlm = get_named_toplevel_module(arg_scope, arg_str_rep)) !== nothing && hasbinding(tlm)
            return bindingof(tlm)
        elseif haskey(par, Symbol(arg_str_rep))
            return par[Symbol(arg_str_rep)]
        end
    elseif par isa SymbolServer.ModuleStore # imported module
        if Symbol(arg_str_rep) === par.name.name
            return par
        elseif haskey(par, Symbol(arg_str_rep))
            par = par[Symbol(arg_str_rep)]
            if par isa SymbolServer.VarRef # reference to dependency
                return SymbolServer._lookup(par, getsymbolserver(state.server), true)
            end
            return par
        end
        for used_module_name in par.used_modules
            used_module = maybe_lookup(par[used_module_name], state.server)
            if used_module !== nothing && isexportedby(Symbol(arg_str_rep), used_module)
                return used_module[Symbol(arg_str_rep)]
            end
        end
    elseif par isa Scope
        if scopehasbinding(par, arg_str_rep)
            return par.names[arg_str_rep]
        elseif par.modules !== nothing
            for used_module in values(par.modules)
                if used_module isa SymbolServer.ModuleStore && isexportedby(Symbol(arg_str_rep), used_module)
                    return maybe_lookup(used_module[Symbol(arg_str_rep)], state.server)
                elseif used_module isa Scope && scope_exports(used_module, arg_str_rep, state)
                    return used_module.names[arg_str_rep]
                end
            end
        end
    elseif par isa Binding
        if par.val isa Binding
            return _get_field(par.val, arg, state)
        elseif par.val isa EXPR && CSTParser.defines_module(par.val) && scopeof(par.val) isa Scope
            return _get_field(scopeof(par.val), arg, state)
        elseif par.val isa SymbolServer.ModuleStore
            return _get_field(par.val, arg, state)
        end
    end
    return
end
