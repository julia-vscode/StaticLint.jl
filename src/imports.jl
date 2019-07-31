function resolve_import(x, state::State)
    u = typof(x) === Using
    i = 2
    n = length(x.args)
    
    root = par = getsymbolserver(state.server)
    bindings = []
    while i <= length(x.args)
        arg = x.args[i]
        if isidentifier(arg) || typof(arg) === CSTParser.MacroName
            if refof(x.args[i]) !== nothing
                par = refof(x.args[i])
            else
                par = _get_field(par, arg, state)
            end
        elseif typof(arg) === PUNCTUATION && kindof(arg) == CSTParser.Tokens.COMMA
            # end of chain, make available
            if i > 2
                _mark_import_arg(x.args[i - 1], par, state, u)
            end
            par = root
        elseif typof(arg) === OPERATOR && kindof(arg) == CSTParser.Tokens.COLON
            root = par
            if par != nothing && i > 2 && isidentifier(x.args[i-1]) && refof(x.args[i-1]) === nothing
                setref!(x.args[i-1], par)
            end
        elseif typof(arg) === PUNCTUATION && kindof(arg) == CSTParser.Tokens.DOT
            #dot between identifiers
            if par != nothing && i > 2 && isidentifier(x.args[i-1]) && refof(x.args[i-1]) === nothing
                setref!(x.args[i-1], par)
            end
        elseif typof(arg) === OPERATOR && kindof(arg) == CSTParser.Tokens.DOT
            #dot prexceding identifiser
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
            _mark_import_arg(x.args[i], par, state, u)
        end
        i += 1
    end
    
end

function _mark_import_arg(arg, par, state, u)
    if par != nothing && (typof(arg) === IDENTIFIER || typof(arg) === MacroName)
        if par isa Binding #mark reference to binding
            push!(par.refs, arg)
        end
        if bindingof(arg) === nothing
            arg.binding = Binding(CSTParser.str_value(arg), par, _typeof(par), [], nothing)
        end
        if u && par isa SymbolServer.ModuleStore
            if state.scope.modules isa Dict
                state.scope.modules[valof(arg)] = par
            else
                state.scope.modules = Dict(valof(arg) => par)
            end
        elseif u && par isa Binding && par.val isa SymbolServer.ModuleStore 
            if state.scope.modules isa Dict
                state.scope.modules[valof(arg)] = par.val
            else
                state.scope.modules = Dict(valof(arg) => par.val)
            end
        elseif u && par isa Binding && par.val isa EXPR && typof(par.val) === CSTParser.ModuleH
            if state.scope.modules isa Dict
                state.scope.modules[valof(arg)] = scopeof(par.val)
            else
                state.scope.modules = Dict(valof(arg) => scopeof(par.val))
            end
        elseif u && par isa Binding && par.val isa Binding && par.val.val isa EXPR && typof(par.val.val) === CSTParser.ModuleH
            if state.scope.modules isa Dict
                state.scope.modules[valof(arg)] = scopeof(par.val.val)
            else
                state.scope.modules = Dict(valof(arg) => scopeof(par.val.val))
            end
            
        end
    end
end


function _get_field(par, arg, state)
    if par isa Dict{String, SymbolServer.ModuleStore} #package store
        if haskey(par, CSTParser.str_value(arg))
            return par[CSTParser.str_value(arg)]
        end
    elseif par isa Scope
        if haskey(par.names, valof(arg))
            return par.names[valof(arg)]
        end
    elseif par isa Binding 
        if par.val isa EXPR && typof(par.val) === ModuleH
            if scopeof(par.val) isa Scope && haskey(scopeof(par.val).names, valof(arg))
                return scopeof(par.val).names[valof(arg)]
            end
        elseif par.val isa SymbolServer.ModuleStore
            if haskey(par.val.vals, CSTParser.str_value(arg))
                par = par.val.vals[CSTParser.str_value(arg)]
                if par isa SymbolServer.PackageRef # reference to dependency
                    return SymbolServer._lookup(par, getsymbolserver(state.server))
                end
                return par
            end
        end
    elseif par isa SymbolServer.ModuleStore # imported module
        if haskey(par.vals, CSTParser.str_value(arg))
            par = par.vals[CSTParser.str_value(arg)]
            if par isa SymbolServer.PackageRef # reference to dependency
                return SymbolServer._lookup(par, getsymbolserver(state.server))
            end
            return par
        end
    end
    return
end

_typeof(x) = nothing
