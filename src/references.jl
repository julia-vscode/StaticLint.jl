function resolve_ref(x, m::File, visited_scopes = 0)
    hasref(x) && return true
    return false
end

function resolve_ref(x, m::Nothing, visited_scopes = 0)
    hasref(x) && return true
    return false
end
function resolve_ref(x, m::T, visited_scopes = 0) where T
    hasref(x) && return true
    @warn "unhandled $T"
    return false
end
function resolve_ref(x1, m::SymbolServer.ModuleStore, visited_scopes = 0)
    hasref(x1) && return true
    if isidentifier(x1)
        x = x1
        if valof(x) == m.name
            setref!(x, m)
            return true
        elseif valof(x) in m.exported && haskey(m.vals, valof(x))
            setref!(x, m.vals[valof(x)])
            return true
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

function resolve_ref(x, scope::Scope, visited_scopes = 0)
    if visited_scopes > 50
        @info "Warning: circular reference found while resolving reference."
        return
    end
    hasref(x) && return true
    resolved = false
    if typof(x) === BinaryOpCall && kindof(x.args[2]) === CSTParser.Tokens.DOT
        return resolve_getindex(x, scope)
    elseif isidentifier(x)
        mn = valof(x)
        x1 = x
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
            resolved = resolve_ref(x, m[2], visited_scopes)
            resolved && break
        end
    end
    if !hasref(x) && !scope.ismodule &&!(parentof(scope) isa EXPR)
        return resolve_ref(x, parentof(scope), visited_scopes)
    end
    return resolved
end

function resolve_getindex(x::EXPR, scope::Scope)
    hasref(x) && return true
    resolved = false
    if typof(x.args[1]) === IDENTIFIER
        resolved = resolve_ref(x.args[1], scope)
        if resolved && typof(x.args[3]) === Quotenode && typof(x.args[3].args[1]) === IDENTIFIER
            resolved = resolve_getindex(x.args[3].args[1], refof(x.args[1]))
        end
    elseif typof(x.args[1]) === BinaryOpCall && kindof(x.args[1].args[2]) === CSTParser.Tokens.DOT
        resolved = resolve_ref(x.args[1], scope)
        if resolved && typof(x.args[3]) === Quotenode && typof(x.args[3].args[1]) === IDENTIFIER
            resolved = resolve_getindex(x.args[3].args[1], refof(x.args[1].args[3].args[1]))
        end
    end
    return resolved
end

function resolve_getindex(x::EXPR, b::Binding)
    hasref(x) && return true
    resolved = false
    if b.t isa Binding
        resolved = resolve_getindex(x, b.t.val)
    elseif b.val isa SymbolServer.ModuleStore
        resolved = resolve_getindex(x, b.val)
    elseif b.val isa EXPR && typof(b.val) === ModuleH
        resolved = resolve_getindex(x, b.val)
    elseif b.val isa Binding && b.val.val isa EXPR && typof(b.val.val) === ModuleH
        resolved = resolve_getindex(x, b.val.val)
    end
    return resolved
end

function resolve_getindex(x::EXPR, parent_type)
    hasref(x) && return true
    return false
end
function resolve_getindex(x::EXPR, parent_type::EXPR)
    hasref(x) && return true
    resolved = false
    if CSTParser.isidentifier(x)
        if (typof(parent_type) === ModuleH || typof(parent_type) === BareModule) && scopeof(parent_type) isa Scope
            resolved = resolve_ref(x, scopeof(parent_type))
        elseif CSTParser.defines_struct(parent_type)
            if haskey(scopeof(parent_type).names, valof(x)) 
                setref!(x, scopeof(parent_type).names[valof(x)])
                push!(bindingof(parent_type).refs, x)
                resolved = true
            end
        end
    end
    return resolved
end

function resolve_getindex(x::EXPR, parent::SymbolServer.SymStore)
    hasref(x) && return true
    resolved = false
    if CSTParser.isidentifier(x)
        if parent isa SymbolServer.ModuleStore && haskey(parent.vals, valof(x))
            setref!(x, parent.vals[valof(x)])
            resolved = true
        elseif parent isa SymbolServer.structStore && valof(x) in parent.fields
        end
    end
    return resolved
end

resolvable_macroname(x) = typof(x) === MacroName && length(x.args) == 2 && isidentifier(x.args[2]) && refof(x.args[2]) === nothing

function hasref(x::EXPR)
    refof(x) !== nothing && refof(x) !== NoReference
end

