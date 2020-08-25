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
function resolve_ref(x, state)
    if !(parentof(x) isa EXPR && typof(parentof(x)) == CSTParser.Quotenode)
        resolved = resolve_ref(x, state.scope, state)
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

function resolve_ref(x::EXPR, scope::Scope, state::State)::Bool
    hasref(x) && return true
    resolved = false

    if is_getfield(x)
        return resolve_getfield(x, scope, state)
    elseif is_kwarg(x)
        # Note to self: this seems wronge - Binding should be attached to entire Kw EXPR.
        if isidentifier(x[1])
            setref!(x[1], Binding(noname, nothing, nothing, [], nothing, nothing))
        elseif is_declaration(x[1]) && isidentifier(x[1][1])
            setref!(x[1][1], Binding(noname, nothing, nothing, [], nothing, nothing))
        end
        return true
    elseif is_special_macro_term(x) || new_within_struct(x)
        setref!(x, Binding(noname, nothing, nothing, [], nothing, nothing))
        return true
    end

    x1, mn = nameof_expr_to_resolve(x)
    mn == true && return true

    if scopehasbinding(scope, mn)
        setref!(x1, scope.names[mn])
        resolved = true
    elseif scope.modules isa Dict && length(scope.modules) > 0
        for m in values(scope.modules)
            resolved = resolve_ref_from_module(x, m, state)
            resolved && return true
        end
    end
    if !resolved && !CSTParser.defines_module(scope.expr) && parentof(scope) isa Scope
        return resolve_ref(x, parentof(scope), state)
    end
    return resolved
end

# Searches a module store for a binding/variable that matches the reference `x1`.
function resolve_ref_from_module(x1::EXPR, m::SymbolServer.ModuleStore, state::State)::Bool
    hasref(x1) && return true
    if isidentifier(x1)
        x = x1
        if Symbol(valof(x)) == m.name.name
            setref!(x, m)
            return true
        elseif isexportedby(x, m)
            setref!(x, maybe_lookup(m[Symbol(valof(x))], state.server))
            return true
        end
    elseif is_macroname(x1)
        x = x1[2]
        if valof(x) == "." && m.name == VarRef(nothing, :Base)
            # @. gets converted to @__dot__, probably during lowering.
            setref!(x, m[:Broadcast][Symbol("@__dot__")])
            return true
        end

        mn = Symbol("@", valof(x))
        if isexportedby(mn, m)
            setref!(x, maybe_lookup(m[mn], state.server))
            return true
        end
    elseif typof(x1) === x_Str
        mac = x1
        mn = Symbol("@", valof(mac[1]), "_str")
        if isexportedby(mn, m)
            setref!(mac[1], maybe_lookup(m[mn], state.server))
            return true
        end
    end
    return false
end

function resolve_ref_from_module(x::EXPR, scope::Scope, state::State)::Bool
    hasref(x) && return true
    resolved = false

    x1, mn = nameof_expr_to_resolve(x)
    mn == true && return true

    if scope_exports(scope, mn, state)
        setref!(x1, scope.names[mn])
        resolved = true
    end
    return resolved
end

"""
    scope_exports(scope::Scope, name::String)

Does the scope export a variable called `name`?
"""
function scope_exports(scope::Scope, name::String, state)
    if scopehasbinding(scope, name) && (b = scope.names[name]) isa Binding
        initial_pass_on_exports(scope.expr, state.server)
        for ref in b.refs
            if ref isa EXPR && parentof(ref) isa EXPR && typof(parentof(ref)) === CSTParser.Export
                return true
            end
        end
    end
    return false
end

"""
    initial_pass_on_exports(x::EXPR, server)

Export statements need to be (pseudo) evaluated each time we consider 
whether a variable is made available by an import statement.
"""
function initial_pass_on_exports(x::EXPR, server)
    # @assert CSTParser.defines_module(x)
    for a in x[3] # module block expressions
        if typof(a) === CSTParser.Export
            traverse(a, Delayed(retrieve_scope(a), server))
        end
    end
end

# Fallback method
function resolve_ref(x::EXPR, m, state::State)::Bool
    return hasref(x)::Bool
end

rhs_of_getfield(x::EXPR) = is_getfield_w_quotenode(x) ? isquoted(x[3]) ? x[3][2] : x[3][1] : x
lhs_of_getfield(x::EXPR) = rhs_of_getfield(x[1])

"""
    resolve_getfield(x::EXPR, parent::Union{EXPR,Scope,ModuleStore,Binding}, state::State)::Bool

Given an expression of the form `parent.x` try to resolve `x`. The method
called with `parent::EXPR` resolves the reference for `parent`, other methods
then check whether the Binding/Scope/ModuleStore to which `parent` points has
a field matching `x`.
"""
function resolve_getfield(x::EXPR, scope::Scope, state::State)::Bool
    hasref(x) && return true
    resolved = resolve_ref(x[1], scope, state)
    if isidentifier(x[1])
        lhs = x[1]
    elseif is_getfield_w_quotenode(x[1])
        lhs = lhs_of_getfield(x)
    else
        return resolved
    end
    if resolved && (rhs = rhs_of_getfield(x)) !== nothing
        resolved = resolve_getfield(rhs, refof(lhs), state)
    end
    return resolved
end


function resolve_getfield(x::EXPR, parent_type::EXPR, state::State)::Bool
    hasref(x) && return true
    resolved = false
    if isidentifier(x)
        if CSTParser.defines_module(parent_type) && scopeof(parent_type) isa Scope
            resolved = resolve_ref(x, scopeof(parent_type), state)
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
    if b.val isa Binding
        resolved = resolve_getfield(x, b.val, state)
    elseif b.val isa SymbolServer.ModuleStore || (b.val isa EXPR && CSTParser.defines_module(b.val))
        resolved = resolve_getfield(x, b.val, state)
    elseif b.type isa Binding
        resolved = resolve_getfield(x, b.type.val, state)
    elseif b.type isa SymbolServer.DataTypeStore
        resolved = resolve_getfield(x, b.type, state)
    end
    return resolved
end

function resolve_getfield(x::EXPR, parent_type, state::State)::Bool
    hasref(x) && return true
    return false
end

function is_overloaded(val::SymbolServer.SymStore, scope::Scope)
    (vr = val.name isa SymbolServer.FakeTypeName ? val.name.name : val.name)
    haskey(scope.overloaded, vr)
end

function resolve_getfield(x::EXPR, m::SymbolServer.ModuleStore, state::State)::Bool
    hasref(x) && return true
    resolved = false
    if isidentifier(x) && (val = maybe_lookup(SymbolServer.maybe_getfield(Symbol(CSTParser.str_value(x)), m, getsymbolserver(state.server)), state.server)) !== nothing
        # Check whether variable is overloaded in top-level scope
        tls = retrieve_toplevel_scope(state.scope)
        if tls.overloaded !== nothing  && (vr = val.name isa SymbolServer.FakeTypeName ? val.name.name : val.name; haskey(tls.overloaded, vr))
            setref!(x, tls.overloaded[vr])
            return true
        end
        setref!(x, val)
        resolved = true
    elseif is_macroname(x) && (val = maybe_lookup(SymbolServer.maybe_getfield(Symbol("@", CSTParser.str_value(x[2])), m, getsymbolserver(state.server)), state.server)) !== nothing
        setref!(x[2], val)
        resolved = true
    end
    return resolved
end

function resolve_getfield(x::EXPR, parent::SymbolServer.DataTypeStore, state::State)::Bool
    hasref(x) && return true
    resolved = false
    if isidentifier(x) && Symbol(valof(x)) in parent.fieldnames
        fi = findfirst(f -> Symbol(valof(x)) == f, parent.fieldnames)
        ft = parent.types[fi]
        val = SymbolServer._lookup(ft, getsymbolserver(state.server), true)
        # TODO: Need to handle the case where we get back a FakeUnion, etc.
        setref!(x, Binding(noname, nothing, val, [], nothing, nothing))
        resolved = true
    end
    return resolved
end

resolvable_macroname(x::EXPR) = is_macroname(x) && isidentifier(x[2]) && refof(x[2]) === nothing

"""
    module_safety_trip(scope::Scope,  visited_scopes)

Checks whether the scope is a module and we've visited it before, 
otherwise adds the module to the list.
"""
function module_safety_trip(scope::Scope,  visited_scopes)
    if CSTParser.defines_module(scope.expr) && length(scope.expr) > 1 && isidentifier(scope.expr[2])
        s_m_name = valofid(scope.expr[2])
        if s_m_name in visited_scopes
            return true
        else
            push!(visited_scopes, s_m_name)
        end
    end
    return false
end


function nameof_expr_to_resolve(x)
    if isidentifier(x)
        x1 = x
        mn = valofid(x)
    elseif resolvable_macroname(x)
        x1 = x[2]
        mn = string("@", valofid(x1))
    elseif typof(x) === x_Str && isidentifier(x[1])
        x1 = x[1]
        mn = string("@", valofid(x1), "_str")
    else
        return x, true
    end
    x1, mn
end

"""
    valofid(x)

Returns the string value of an expression for which `isidentifier` is true, 
i.e. handles NONSTDIDENTIFIERs.
"""
valofid(x::EXPR) = typof(x) === CSTParser.IDENTIFIER ? valof(x) : valof(x[2])

"""
new_within_struct(x::EXPR)

Checks whether x is a reference to `new` within a datatype constructor. 
"""
new_within_struct(x::EXPR) = isidentifier(x) && valofid(x) == "new" && is_in_fexpr(x, CSTParser.defines_struct)
is_special_macro_term(x::EXPR) = isidentifier(x) && (valofid(x) == "__source__" || valofid(x) == "__module__") && is_in_fexpr(x, CSTParser.defines_macro)