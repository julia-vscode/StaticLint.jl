function resolve_ref(x, m::File)
    hasref(x) && return true
    return false
end

function resolve_ref(x, m::Nothing) 
    hasref(x) && return true
    return false
end
function resolve_ref(x, m::T) where T
    hasref(x) && return true
    @warn "unhandled $T"
    return false
end
function resolve_ref(x1, m::SymbolServer.ModuleStore)
    hasref(x1) && return true
    if isidentifier(x1)
        x = x1
        if x.val == m.name
            x.ref = m
            return true
        elseif x.val in m.exported && haskey(m.vals, x.val)
            x.ref = m.vals[x.val]
            return true
        end
    elseif x1.typ === MacroName
        x = x1.args[2]
        mn = string("@", x.val)
        if mn in m.exported
            x.ref = m.vals[mn]
            return true
        end
    elseif x1.typ === x_Str
        mac = x1
        mn = string("@", mac.args[1].val, "_str")
        if mn in m.exported && haskey(m.vals, mn)
            mac.args[1].ref = m.vals[mn]
            return true
        end
    end
    return false
end

function resolve_ref(x, scope::Scope)
    hasref(x) && return true
    resolved = false
    if x.typ === BinaryOpCall && x.args[2].kind === CSTParser.Tokens.DOT
        return resolve_getindex(x, scope)
    elseif isidentifier(x)
        mn = x.val
        x1 = x
    elseif x.typ === MacroName
        x1 = x.args[2]
        mn = string("@", x1.val)
    elseif x.typ === x_Str
        x1 = x.args[1]
        mn = string("@", x1.val)
    end
    
    if haskey(scope.names, mn)
        x1.ref = scope.names[mn]
        push!(scope.names[mn].refs, x1)
        resolved = true
    elseif scope.modules isa Dict && length(scope.modules) > 0
        for m in scope.modules
            resolved = resolve_ref(x, m[2])
            resolved && break
        end
    end
    if !hasref(x) && !(scope.parent isa EXPR)
        return resolve_ref(x, scope.parent)
    end
    return resolved
end

function resolve_getindex(x, scope::Scope)
    hasref(x) && return true
    resolved = false
    if x.args[1].typ === IDENTIFIER
        resolved = resolve_ref(x.args[1], scope)
        if resolved && x.args[3].typ === Quotenode && x.args[3].args[1].typ === IDENTIFIER
            resolved = resolve_getindex(x.args[3].args[1], x.args[1].ref)
        end
    end
    return resolved
end
resolve_getindex(x::EXPR, b::Binding) = resolve_getindex(x, b.val)
function resolve_getindex(x::EXPR, parent::EXPR)
    hasref(x) && return true
    resolved = false
    if CSTParser.isidentifier(x)
        if (parent.typ === ModuleH || parent.typ === BareModule) && parent.scope isa Scope
            resolved = resolve_ref(x, parent.scope)
        end
    end
    return resolved
end

function resolve_getindex(x::EXPR, parent::SymbolServer.SymStore)
    hasref(x) && return true
    resolved = false
    if CSTParser.isidentifier(x)
        if haskey(parent.vals, x.val)
            x.ref = parent.vals[x.val]
            resolved = true
        end
    end
    return resolved
end

resolvable_macroname(x) = x.typ === MacroName && length(x.args) == 2 && isidentifier(x.args[2]) && x.args[2].ref === nothing

function hasref(x::EXPR)
    x.ref !== nothing && x.ref !== NoReference
end
