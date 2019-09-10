function resolve_ref(x, m::File, state::State, visited_scopes = 0)
    hasref(x) && return true
    return false
end

function resolve_ref(x, m::Nothing, state::State, visited_scopes = 0)
    hasref(x) && return true
    return false
end
function resolve_ref(x, m::T, state::State, visited_scopes = 0) where T
    hasref(x) && return true
    @warn "unhandled $T"
    return false
end
function resolve_ref(x1, m::SymbolServer.ModuleStore, state::State, visited_scopes = 0)
    hasref(x1) && return true
    if isidentifier(x1)
        x = x1
        if valof(x) == m.name
            setref!(x, m)
            return true
        elseif valof(x) in m.exported && haskey(m.vals, valof(x))
            val = m.vals[valof(x)]
            if val isa SymbolServer.PackageRef
                val1 = SymbolServer._lookup(val, getsymbolserver(state.server))
                if val1 !== nothing
                    setref!(x, val1)
                    return true
                else
                    return false
                end
            else
                setref!(x, val)
                return true
            end
        end
    elseif typof(x1) === MacroName
        x = x1.args[2]
        mn = string("@", valof(x))
        if mn in m.exported
            setref!(x, m.vals[mn])
            return true
        end
    elseif typof(x1) === x_Str
        mac = x1
        mn = string("@", valof(mac.args[1]), "_str")
        if mn in m.exported && haskey(m.vals, mn)
            setref!(mac.args[1], m.vals[mn])
            return true
        end
    end
    return false
end

function resolve_ref(x, scope::Scope, state::State, visited_scopes = 0)
    if visited_scopes > 50
        @info "Warning: circular reference found while resolving reference."
        return false
    end
    hasref(x) && return true
    resolved = false
    if typof(x) === BinaryOpCall && kindof(x.args[2]) === CSTParser.Tokens.DOT
        return resolve_getindex(x, scope, state)
    elseif isidentifier(x)
        mn = valof(x)
        x1 = x
        if (mn == "__source__" || mn == "__module__") && _in_macro_def(x)
            setref!(x, NoReference)
            return true
        end
    elseif typof(x) === MacroName
        x1 = x.args[2]
        mn = string("@", valof(x1))
    elseif typof(x) === x_Str
        if typof(x.args[1]) === IDENTIFIER
            x1 = x.args[1]
            mn = string("@", valof(x1), "_str")
        else
            return false
        end
    else
        return false
    end
    
    if haskey(scope.names, mn)
        setref!(x1, scope.names[mn])
        push!(scope.names[mn].refs, x1)
        resolved = true
    elseif scope.modules isa Dict && length(scope.modules) > 0
        for m in scope.modules
            resolved = resolve_ref(x, m[2], state, visited_scopes + 1)
            resolved && break
        end
    end
    if !hasref(x) && !scope.ismodule &&!(parentof(scope) isa EXPR)
        return resolve_ref(x, parentof(scope), state, visited_scopes + 1)
    end
    return resolved
end

function resolve_getindex(x::EXPR, scope::Scope, state::State)
    hasref(x) && return true
    resolved = false
    if typof(x.args[1]) === IDENTIFIER
        resolved = resolve_ref(x.args[1], scope, state)
        if resolved && typof(x.args[3]) === Quotenode && typof(x.args[3].args[1]) === IDENTIFIER
            resolved = resolve_getindex(x.args[3].args[1], refof(x.args[1]), state)
        end
    elseif typof(x.args[1]) === BinaryOpCall && kindof(x.args[1].args[2]) === CSTParser.Tokens.DOT
        resolved = resolve_ref(x.args[1], scope, state)
        if resolved && typof(x.args[3]) === Quotenode && typof(x.args[3].args[1]) === IDENTIFIER
            resolved = resolve_getindex(x.args[3].args[1], refof(x.args[1].args[3].args[1]), state)
        end
    end
    return resolved
end

function resolve_getindex(x::EXPR, b::Binding, state::State)
    hasref(x) && return true
    resolved = false
    if b.t isa Binding
        resolved = resolve_getindex(x, b.t.val, state)
    elseif b.val isa SymbolServer.ModuleStore
        resolved = resolve_getindex(x, b.val, state)
    elseif b.val isa EXPR && typof(b.val) === ModuleH
        resolved = resolve_getindex(x, b.val, state)
    elseif b.val isa Binding && b.val.val isa EXPR && typof(b.val.val) === ModuleH
        resolved = resolve_getindex(x, b.val.val, state)
    end
    return resolved
end

function resolve_getindex(x::EXPR, parent_type, state::State)
    hasref(x) && return true
    return false
end
function resolve_getindex(x::EXPR, parent_type::EXPR, state::State)
    hasref(x) && return true
    resolved = false
    if CSTParser.isidentifier(x)
        if (typof(parent_type) === ModuleH || typof(parent_type) === BareModule) && scopeof(parent_type) isa Scope
            resolved = resolve_ref(x, scopeof(parent_type), state)
        elseif CSTParser.defines_struct(parent_type)
            if haskey(scopeof(parent_type).names, valof(x)) 
                setref!(x, scopeof(parent_type).names[valof(x)])
                push!(scopeof(parent_type).names[valof(x)].refs, x)
                # push!(bindingof(parent_type).refs, x)
                resolved = true
            end
        end
    end
    return resolved
end

function resolve_getindex(x::EXPR, parent::SymbolServer.SymStore, state::State)
    hasref(x) && return true
    resolved = false
    if CSTParser.isidentifier(x)
        if parent isa SymbolServer.ModuleStore && haskey(parent.vals, valof(x))
            val = parent.vals[valof(x)]
            if val isa SymbolServer.PackageRef
                val = SymbolServer._lookup(val, getsymbolserver(state.server))
                val === nothing && return false
            end
            setref!(x, val)
            resolved = true
        elseif parent isa SymbolServer.DataTypeStore && valof(x) in parent.fields
        end
    end
    return resolved
end

resolvable_macroname(x) = typof(x) === MacroName && length(x.args) == 2 && isidentifier(x.args[2]) && refof(x.args[2]) === nothing

function hasref(x::EXPR)
    refof(x) !== nothing && refof(x) !== NoReference
end

function _in_macro_def(x)
    if typof(x) === CSTParser.Macro
        return true
    elseif parentof(x) isa EXPR
        return _in_macro_def(parentof(x))
    else
        return false
    end
end