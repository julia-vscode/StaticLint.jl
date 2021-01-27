function resolve_import_block(x::EXPR, state::State, root, usinged, markfinal=true)
    n = length(x.args)
    for i = 1:length(x.args)
        arg = x.args[i]
        if isoperator(arg) && valof(arg) == "."
            # Leading dots. Can only be leading elements.
            if root == getsymbols(state)
                root = state.scope
            elseif root isa Scope && parentof(root) !== nothing
                root = parentof(root)
            else
                return
            end
        elseif isidentifier(arg) || (i == n && (CSTParser.ismacroname(arg) || isoperator(arg)))
            root = maybe_lookup(hasref(arg) ? refof(arg) : _get_field(root, arg, state), state.server)
            setref!(arg, root)
            if i == n
                markfinal && _mark_import_arg(arg, root, state, usinged)
                return refof(arg)
            end
        else
            return 
        end
    end
end

function resolve_import(x::EXPR, state::State, root=getsymbols(state))
    if headof(x) === :using || headof(x) === :import
        usinged = headof(x) === :using
        if length(x.args) > 0 && isoperator(headof(x.args[1])) && valof(headof(x.args[1])) == ":"
            root = resolve_import_block(x.args[1].args[1], state, root, false, false)
            for i = 2:length(x.args[1].args)
                resolve_import_block(x.args[1].args[i], state, root, usinged)
            end
        else
            for i = 1:length(x.args)
                resolve_import_block(x.args[i], state, root, usinged)
            end
        end
    end
end

function _mark_import_arg(arg, par, state, usinged)
    if par !== nothing && CSTParser.is_id_or_macroname(arg)
        if par isa Binding # mark reference to binding
            push!(par.refs, arg)
        end
        if par isa SymbolServer.VarRef
            par = SymbolServer._lookup(par, getsymbols(state), true)
            !(par isa SymbolServer.SymStore) && return
        end
        if bindingof(arg) === nothing
            if !hasmeta(arg)
                arg.meta = Meta()
            end
            arg.meta.binding = Binding(arg, par, _typeof(par, state), [])
            setref!(arg, bindingof(arg))
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
    if CSTParser.defines_module(s.expr) 
        m_name = CSTParser.get_name(s.expr)
        if CSTParser.isidentifier(m_name) && valofid(m_name) == name && no_modules_above(s)
            return s.expr
        end
    end
    if s.parent isa Scope
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
                return SymbolServer._lookup(par, getsymbols(state), true)
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
