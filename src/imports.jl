function resolve_import(x, state::State)
    if typof(x) === Using || typof(x) === Import
        u = typof(x) === Using
        i = 2
        n = length(x)
        
        root = par = getsymbolserver(state.server)
        bindings = []
        while i <= n
            arg = x[i]
            if isidentifier(arg) || typof(arg) === CSTParser.MacroName
                if refof(arg) !== nothing
                    par = refof(arg)
                else
                    par = _get_field(par, arg, state)
                end
            elseif typof(arg) === PUNCTUATION && kindof(arg) == CSTParser.Tokens.COMMA
                # end of chain, make available
                if i > 2
                    _mark_import_arg(x[i - 1], par, state, u)
                end
                par = root
            elseif typof(arg) === OPERATOR && kindof(arg) == CSTParser.Tokens.COLON
                root = par
                if par !== nothing && i > 2 && isidentifier(x[i - 1]) && refof(x[i - 1]) === nothing
                    setref!(x[i - 1], par)
                end
            elseif typof(arg) === PUNCTUATION && kindof(arg) == CSTParser.Tokens.DOT
                # dot between identifiers
                if par !== nothing && i > 2 && isidentifier(x[i - 1]) && refof(x[i - 1]) === nothing
                    setref!(x[i - 1], par)
                end
            elseif typof(arg) === OPERATOR && kindof(arg) == CSTParser.Tokens.DOT
                # dot prexceding identifiser
                if par == root == getsymbolserver(state.server)
                    par = state.scope
                elseif par isa Scope && parentof(par) !== nothing
                    par = parentof(par)
                else
                    return
                end
            else
                return
            end
            if i == n 
                _mark_import_arg(x[i], par, state, u)
            end
            i += 1
        end
    end
end

function _mark_import_arg(arg, par, state, u)
    if par !== nothing && (typof(arg) === IDENTIFIER || typof(arg) === MacroName)
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
        if u && par isa SymbolServer.ModuleStore
            if state.scope.modules isa Dict
                state.scope.modules[Symbol(valof(arg))] = par
            else
                state.scope.modules = Dict(Symbol(valof(arg)) => par)
            end
        elseif u && par isa Binding && par.val isa SymbolServer.ModuleStore 
            if state.scope.modules isa Dict
                state.scope.modules[Symbol(valof(arg))] = par.val
            else
                state.scope.modules = Dict(Symbol(valof(arg)) => par.val)
            end
        elseif u && par isa Binding && par.val isa EXPR && (typof(par.val) === CSTParser.ModuleH || typof(par.val) === CSTParser.BareModule)
            if state.scope.modules isa Dict
                state.scope.modules[Symbol(valof(arg))] = scopeof(par.val)
            else
                state.scope.modules = Dict(Symbol(valof(arg)) => scopeof(par.val))
            end
        elseif u && par isa Binding && par.val isa Binding && par.val.val isa EXPR && (typof(par.val.val) === CSTParser.ModuleH || typof(par.val.val) === CSTParser.BareModule)
            if state.scope.modules isa Dict
                state.scope.modules[Symbol(valof(arg))] = scopeof(par.val.val)
            else
                state.scope.modules = Dict(Symbol(valof(arg)) => scopeof(par.val.val))
            end
        end
    end
end

function _get_field(par, arg, state)
    arg_str_rep = CSTParser.str_value(arg)
    if par isa SymbolServer.EnvStore && haskey(par, Symbol(arg_str_rep))
        return par[Symbol(arg_str_rep)]
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
    elseif par isa Scope && scopehasbinding(par, arg_str_rep)
        return par.names[arg_str_rep]
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
