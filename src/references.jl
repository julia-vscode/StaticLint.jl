function setref!(x::EXPR, binding::Binding)
    if !hasmeta(x)
        x.meta = Meta()
    end
    x.meta.ref = binding
    binding.refs !== nothing && push!(binding.refs, x)
end

function setref!(x::EXPR, binding)
    if !hasmeta(x)
        x.meta = Meta()
    end
    x.meta.ref = binding
end


# Main function to be called. Given the `state` tries to determine what `x` 
# refers to. If it remains unresolved and is in a delayed evaluation scope 
# (i.e. a function) it gets pushed to list (.urefs) to be resolved after we've
# run over the entire top-level scope.
function _resolve_ref(x, state)
    if !(parentof(x) isa EXPR && typof(parentof(x)) == CSTParser.Quotenode)
        resolved = resolve_ref(x, state.scope, state, [])
        if !resolved && (state.delayed || isglobal(valof(x), state.scope))
            push!(state.urefs, x)
        end
    end
end


# The first method that is tried. Searches the current scope for local bindings
# that match `x`. Steps:
# 1. Check whether we've already checked this scope (inifinite loops are
# possible when traversing nested modules.)
# 2. Check what sort of EXPR we're dealing with, separate name from EXPR that
# binds.
# 3. Look in the scope's variable list for a binding matching the name.
# 4. If 3. is unsuccessful, check whether the scope imports any modules then check them.
# 5. If no match is found within this scope check the parent scope.
# The return value is a boolean that is false if x should point to something but 
# can't be resolved. 
 
function resolve_ref(x::EXPR, scope::Scope, state::State, visited_scopes)::Bool
    hasref(x) && return true
    resolved = false
    module_safety_trip(scope, visited_scopes) && return false
    
    if is_getfield(x)
        return resolve_getfield(x, scope, state)
    elseif isidentifier(x)
        if typof(x) === IDENTIFIER
            mn = valof(x)
            x1 = x
        else
            # NONSTDIDENTIFIER, e.g. var"name"
            mn = valof(x[2])
            x1 = x
        end
        if (mn == "__source__" || mn == "__module__") && _in_macro_def(x)
            setref!(x, Binding(noname, nothing, nothing, [], nothing, nothing))
            return true
        end
    elseif resolvable_macroname(x)
        x1 = x[2]
        mn = string("@", valof(x1))
    elseif typof(x) === x_Str
        if typof(x[1]) === IDENTIFIER
            x1 = x[1]
            mn = string("@", valof(x1), "_str")
        else
            return false
        end
    elseif typof(x) === CSTParser.Kw
        # Note to self: this seems wronge - Binding should be attached to entire Kw EXPR.
        if typof(x[1]) === IDENTIFIER
            setref!(x[1], Binding(noname, nothing, nothing, [], nothing, nothing))
        elseif typof(x[1]) === BinaryOpCall && kindof(x[1][2]) === CSTParser.Tokens.DECLARATION && typof(x[1][1]) === IDENTIFIER
            setref!(x[1][1], Binding(noname, nothing, nothing, [], nothing, nothing))
        end
        return true
    else
        return true
    end
    if scopehasbinding(scope, mn)
        setref!(x1, scope.names[mn])
        resolved = true
    elseif scope.modules isa Dict && length(scope.modules) > 0
        for m in scope.modules
            resolved = resolve_ref_from_module(x, m[2], state, visited_scopes)
            resolved && return true
        end
    end
    if !resolved && !scope.ismodule && parentof(scope) isa Scope
        return resolve_ref(x, parentof(scope), state, visited_scopes)
    end
    return resolved
end

# Searches a module store for a binding/variable that matches the reference `x1`.
function resolve_ref_from_module(x1::EXPR, m::SymbolServer.ModuleStore, state::State, visited_scopes)::Bool
    hasref(x1) && return true
    if isidentifier(x1)
        x = x1
        if Symbol(valof(x)) == m.name.name
            setref!(x, m)
            return true
        elseif isexportedby(x, m)
            val = m[Symbol(valof(x))]
            if val isa SymbolServer.VarRef
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
        x = x1[2]
        mn = Symbol("@", valof(x))
        if isexportedby(mn, m)
            setref!(x, m[mn])
            return true
        end
    elseif typof(x1) === x_Str
        mac = x1
        mn = Symbol("@", valof(mac[1]), "_str")
        if isexportedby(mn, m)
            setref!(mac[1], m[mn])
            return true
        end
    end
    return false
end

function resolve_ref_from_module(x::EXPR, scope::Scope, state::State, visited_scopes)::Bool
    hasref(x) && return true
    resolved = false
    module_safety_trip(scope, visited_scopes) && return false

    if isidentifier(x)
        if typof(x) === IDENTIFIER
            mn = valof(x)
            x1 = x
        else
            # NONSTDIDENTIFIER, e.g. var"name"
            mn = valof(x[2])
            x1 = x
        end
    elseif resolvable_macroname(x)
        x1 = x[2]
        mn = string("@", valof(x1))
    elseif typof(x) === x_Str
        if typof(x[1]) === IDENTIFIER
            x1 = x[1]
            mn = string("@", valof(x1), "_str")
        else
            return false
        end
    else
        return true # TODO: Should be false?
    end

    if scope_exports(scope, mn)
        setref!(x1, scope.names[mn])
        resolved = true
    end
    return resolved
end

"""
    scope_exports(scope::Scope, name::String)

Does the scope export a variable called `name`?
"""
function scope_exports(scope::Scope, name::String)
    if scopehasbinding(scope, name) && (b = scope.names[name]) isa Binding
        for ref in b.refs
            if ref isa EXPR && parentof(ref) isa EXPR && typof(parentof(ref)) === CSTParser.Export
                return true
            end
        end
    end
    return false
end

# Fallback method
function resolve_ref(x::EXPR, m, state::State, visited_scopes)::Bool
    return hasref(x)::Bool
end


"""
    resolve_getfield(x::EXPR, parent::Union{EXPR,Scope,ModuleStore,Binding}, state::State)::Bool

Given an expression of the form `parent.x` try to resolve `x`. The method
called with `parent::EXPR` resolves the reference for `parent`, other methods
then check whether the Binding/Scope/ModuleStore to which `parent` points has
a field matching `x`.
"""
function resolve_getfield(x::EXPR, scope::Scope, state::State)::Bool
    hasref(x) && return true
    resolved = false
    if isidentifier(x[1])
        resolved = resolve_ref(x[1], scope, state, [])
        if resolved && typof(x[3]) === Quotenode && isidentifier(x[3][1])
            resolved = resolve_getfield(x[3][1], refof(x[1]), state)
        end
    elseif is_getfield_w_quotenode(x[1])
        resolved = resolve_ref(x[1], scope, state, [])
        if resolved && typof(x[3]) === Quotenode && length(x[3]) > 0 && isidentifier(x[3][1])
            resolved = resolve_getfield(x[3][1], refof(x[1][3][1]), state)
        end
    end
    return resolved
end


function resolve_getfield(x::EXPR, parent_type::EXPR, state::State)::Bool
    hasref(x) && return true
    resolved = false
    if CSTParser.isidentifier(x)
        if CSTParser.defines_module(parent_type) && scopeof(parent_type) isa Scope
            resolved = resolve_ref(x, scopeof(parent_type), state, [])
        elseif CSTParser.defines_struct(parent_type)
            if scopehasbinding(scopeof(parent_type), valof(x)) 
                setref!(x, scopeof(parent_type).names[valof(x)])
                resolved = true
            end
        end
    end
    return resolved
end


function resolve_getfield(x::EXPR, b::Binding, state::State)::Bool
    hasref(x) && return true
    resolved = false
    if b.type isa Binding
        resolved = resolve_getfield(x, b.type.val, state)
    elseif b.val isa SymbolServer.ModuleStore
        resolved = resolve_getfield(x, b.val, state)
    elseif b.type isa SymbolServer.DataTypeStore
        resolved = resolve_getfield(x, b.type, state)
    elseif b.val isa EXPR && CSTParser.defines_module(b.val)
        resolved = resolve_getfield(x, b.val, state)
    elseif b.val isa Binding && b.val.val isa EXPR && CSTParser.defines_module(b.val.val)
        resolved = resolve_getfield(x, b.val.val, state)
    end
    return resolved
end

function resolve_getfield(x::EXPR, parent_type, state::State)::Bool
    hasref(x) && return true
    return false
end

function resolve_getfield(x::EXPR, m::SymbolServer.ModuleStore, state::State)::Bool
    hasref(x) && return true
    resolved = false
    if CSTParser.isidentifier(x) && haskey(m, Symbol(valof(x)))
        val = m[Symbol(valof(x))]
        if val isa SymbolServer.VarRef
            val = SymbolServer._lookup(val, getsymbolserver(state.server))
            !(val isa SymbolServer.SymStore) && return false
        end
        setref!(x, val)
        resolved = true
    end
    return resolved
end

function resolve_getfield(x::EXPR, parent::SymbolServer.DataTypeStore, state::State)::Bool
    hasref(x) && return true
    resolved = false
    if CSTParser.isidentifier(x) && Symbol(valof(x)) in parent.fieldnames
        fi = findfirst(f->Symbol(valof(x)) == f, parent.fieldnames)
        ft = parent.types[fi]
        val = SymbolServer._lookup(ft, getsymbolserver(state.server))
        if val !== nothing
            setref!(x, Binding(noname, nothing, val, [], nothing, nothing))
            resolved = true
        end
    end
    return resolved
end

resolvable_macroname(x::EXPR) = typof(x) === MacroName && length(x) == 2 && isidentifier(x[2]) && refof(x[2]) === nothing

function _in_macro_def(x::EXPR)
    if typof(x) === CSTParser.Macro
        return true
    elseif parentof(x) isa EXPR
        return _in_macro_def(parentof(x))
    else
        return false
    end
end

"""
    module_safety_trip(scope::Scope,  visited_scopes)

Checks whether the scope is a module and we've visited it before, 
otherwise adds the module to the list.
"""
function module_safety_trip(scope::Scope,  visited_scopes)
    if CSTParser.defines_module(scope.expr) && CSTParser.length(scope.expr) > 1 && CSTParser.typof(scope.expr[2]) === IDENTIFIER
        s_m_name = scope.expr[2].val isa String ? scope.expr[2].val : ""
        if s_m_name in visited_scopes
            return true
        else
            push!(visited_scopes, s_m_name)
        end
    end
    return false
end
