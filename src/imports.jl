function resolve_import(x, state::State)
    u = x.typ === Using
    i = 2
    n = length(x.args)
    
    root = par = getsymbolserver(state.server)
    bindings = []
    while i <= length(x.args)
        arg = x.args[i]
        if isidentifier(arg) || arg.typ === CSTParser.MacroName
            if x.args[i].ref !== nothing
                par = x.args[i].ref
            else
                par = _get_field(par, arg, state)
            end
            # if par == nothing
            #     return
            # end
        elseif arg.typ === PUNCTUATION && arg.kind == CSTParser.Tokens.COMMA
            # end of chain, make available
            if i > 2 && isidentifier(x.args[i-1]) && par != nothing# && x.args[i-1].ref === nothing
                if par isa Binding #mark reference to binding
                    push!(par.refs, x.args[i-1])
                end
                if x.args[i-1].binding === nothing
                    x.args[i-1].binding = Binding(CSTParser.str_value(x.args[i-1]), par, _typeof(par), [], nothing)
                end
                if u && par isa SymbolServer.ModuleStore
                    if state.scope.modules isa Dict
                        state.scope.modules[x.args[i-1].val] = par
                    else
                        state.scope.modules = Dict(x.args[i-1].val => par)
                    end
                elseif u && par isa Binding && par.val isa SymbolServer.ModuleStore 
                    if state.scope.modules isa Dict
                        state.scope.modules[x.args[i-1].val] = par.val
                    else
                        state.scope.modules = Dict(x.args[i-1].val => par.val)
                    end
                elseif u && par isa Binding && par.val isa EXPR && par.val.typ === CSTParser.ModuleH
                    if state.scope.modules isa Dict
                        state.scope.modules[x.args[i-1].val] = par.val.scope
                    else
                        state.scope.modules = Dict(x.args[i-1].val => par.val.scope)
                    end
                end
            end
            par = root
        elseif arg.typ === OPERATOR && arg.kind == CSTParser.Tokens.COLON            
            root = par
            if par != nothing && i > 2 && isidentifier(x.args[i-1]) && x.args[i-1].ref === nothing
                x.args[i-1].ref = par
            end
        elseif arg.typ === PUNCTUATION && arg.kind == CSTParser.Tokens.DOT
            #dot between identifiers
            if par != nothing && i > 2 && isidentifier(x.args[i-1]) && x.args[i-1].ref === nothing
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
        if i == n && par != nothing && x.args[i].typ === IDENTIFIER # && x.args[i].ref === nothing
            if par isa Binding #mark reference to binding
                push!(par.refs, x.args[i])
            end
            if x.args[i].binding === nothing
                x.args[i].binding = Binding(CSTParser.str_value(x.args[i]), par, _typeof(par), [], nothing)
            end
            if u && par isa SymbolServer.ModuleStore
                if state.scope.modules isa Dict
                    state.scope.modules[x.args[i].val] = par
                else
                    state.scope.modules = Dict(x.args[i].val => par)
                end
            elseif u && par isa Binding && par.val isa SymbolServer.ModuleStore 
                if state.scope.modules isa Dict
                    state.scope.modules[x.args[i].val] = par.val
                else
                    state.scope.modules = Dict(x.args[i].val => par.val)
                end
            elseif u && par isa Binding && par.val isa EXPR && par.val.typ === CSTParser.ModuleH
                if state.scope.modules isa Dict
                    state.scope.modules[x.args[i].val] = par.val.scope
                else
                    state.scope.modules = Dict(x.args[i].val => par.val.scope)
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
    elseif par isa Binding 
        if par.val isa EXPR && par.val.typ === ModuleH
            if par.val.scope isa Scope && haskey(par.val.scope.names, arg.val)
                return par.val.scope.names[arg.val]
            end
        elseif par.val isa SymbolServer.ModuleStore
            if haskey(par.val.vals, CSTParser.str_value(arg))
                par = par.val.vals[CSTParser.str_value(arg)]
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
