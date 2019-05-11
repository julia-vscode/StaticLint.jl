function _import_ismodule(par)
    par isa SymbolServer.ModuleStore
end

function resolve_import(x, state)
    u = x.typ === Using
    i = 2
    n = length(x.args)
    
    root = par = getsymbolserver(state.server)
    bindings = []
    while i <= length(x.args)
        arg = x.args[i]
        if isidentifier(arg)
            par = _get_field(par, arg, state)
            if par == nothing
                return
            end
        elseif arg.typ === PUNCTUATION && arg.kind == CSTParser.Tokens.COMMA
            # end of chain, make available
            if i > 2 && isidentifier(x.args[i-1]) && par != nothing
                x.args[i-1].binding = Binding(x.args[i-1].val, par, _typeof(par), [], nothing)
                if _import_ismodule(par) && u
                    if state.scope.modules isa Dict
                        state.scope.modules[x.args[i-1].val] = par
                    else
                        state.scope.modules = Dict(x.args[i-1].val => par)
                    end
                end
            end
            par = root
        elseif arg.typ === OPERATOR && arg.kind == CSTParser.Tokens.COLON            
            root = par
            if par != nothing && i > 2 && isidentifier(x.args[i-1])
                x.args[i-1].ref = par
            end
        elseif arg.typ === PUNCTUATION && arg.kind == CSTParser.Tokens.DOT
            #dot between identifiers
            if par != nothing && i > 2 && isidentifier(x.args[i-1])
                x.args[i-1].ref = par
            end
        elseif arg.typ === OPERATOR && arg.kind == CSTParser.Tokens.DOT
            #dot prexceding identifiser
            if par == root == getsymbolserver(state.server)
                par = state.scope
            elseif par isa Scope && par.parent !== nothing
                par = par.parent
            else
                return
            end
        else
            return
        end
        if i == n && par != nothing
            x.args[i].binding = Binding(x.args[i].val, par, _typeof(par), [], nothing)
            if _import_ismodule(par) && u
                if state.scope.modules isa Dict
                    state.scope.modules[x.args[i].val] = par
                else
                    state.scope.modules = Dict(x.args[i].val => par)
                end
            end
        end
        i += 1
    end
    
end

function _get_field(par, arg, state)
    if par isa Dict{String, SymbolServer.ModuleStore} #package store
        if haskey(par, CSTParser.str_value(arg))
            par = par[CSTParser.str_value(arg)]
            if par isa String # reference to dependency
                if haskey(getsymbolserver(state.server), par)
                    return getsymbolserver(state.server)[par] 
                else
                    return
                end
            end
            return par
        end
    elseif par isa Scope
        if haskey(par.names, arg.val)
            return par.names[arg.val]
        end
    elseif par isa Binding && par.val.typ === ModuleH
        if par.val.scope isa Scope && haskey(par.val.scope.names, arg.val)
            return par.val.scope.names[arg.val]
        end
    elseif par isa SymbolServer.ModuleStore # imported module
        if haskey(par.vals, CSTParser.str_value(arg))
            par = par.vals[CSTParser.str_value(arg)]
            if par isa String # reference to dependency
                if haskey(getsymbolserver(state.server), par)
                    return getsymbolserver(state.server)[par] 
                else
                    return 
                end
            end
            return par
        end
    end
    return
end

_typeof(x) = nothing
