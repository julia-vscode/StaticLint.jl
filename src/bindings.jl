mutable struct Binding
    name::EXPR
    val::Union{Binding,EXPR,SymbolServer.SymStore,Nothing}
    type::Union{Binding,EXPR,SymbolServer.SymStore,Nothing}
    refs::Vector{Any}
    prev::Union{Binding,SymbolServer.SymStore,Nothing}
    next::Union{Binding,SymbolServer.SymStore,Nothing}
end
Binding(x::EXPR) = Binding(CSTParser.get_name(x), x, nothing, [], nothing, nothing)

function Base.show(io::IO, b::Binding)
    printstyled(io, "Binding(", Expr(b.name),
        b.type === nothing ? "" : ":: ",
        b.refs isa Vector ? "($(length(b.refs)) refs))" : ")", color = :blue)
end


hasbinding(x::EXPR) = hasmeta(x) && hasbinding(x.meta)
bindingof(x) = nothing
bindingof(x::EXPR) = bindingof(x.meta)


hasref(x::EXPR) = hasmeta(x) && hasref(x.meta)
refof(x::EXPR) = hasmeta(x) ? x.meta.ref : nothing


function gotoobjectofref(x::EXPR)
    r = refof(x)
    if r isa SymbolServer.SymStore
        return r
    elseif r isa Binding

    end
end


# Note to self, check consistency of marking self-reference of bindings (i.e.
# for, `function f end` we resolve `f` to itself at this stage.)
function mark_bindings!(x::EXPR, state)
    if hasbinding(x)
        return
    end
    if !hasmeta(x)
        x.meta = Meta()
    end
    if typof(x) === BinaryOpCall
        if kindof(x[2]) === CSTParser.Tokens.EQ
            if CSTParser.is_func_call(x[1])
                name = CSTParser.get_name(x)
                mark_binding!(x)
                mark_sig_args!(x[1])
                if typof(name) === IDENTIFIER
                    setref!(name, bindingof(x))
                end
            elseif typof(x[1]) === CSTParser.Curly
                mark_typealias_bindings!(x)
            else
                mark_binding!(x[1], x)
            end
        elseif kindof(x[2]) === CSTParser.Tokens.ANON_FUNC
            mark_binding!(x[1], x)
        end
    elseif typof(x) === WhereOpCall
        for i = 3:length(x)
            typof(x[i]) === PUNCTUATION && continue
            mark_binding!(x[i])
        end
    elseif typof(x) === CSTParser.For
        markiterbinding!(x[2])
    elseif typof(x) === CSTParser.Generator
        for i = 3:length(x)
            typof(x[i]) === PUNCTUATION && continue
            markiterbinding!(x[i])
        end
    elseif typof(x) === CSTParser.Filter
        for i = 1:length(x) - 2
            typof(x[i]) === PUNCTUATION && continue
            markiterbinding!(x[i])
        end
    elseif typof(x) === CSTParser.Flatten && length(x) === 1 && length(x[1]) >= 3 && length(x[1][1]) >= 3
        for i = 3:length(x[1][1])
            typof(x[1][1][i]) === PUNCTUATION && continue
            markiterbinding!(x[1][1][i])
        end
        for i = 3:length(x[1])
            typof(x[1][i]) === PUNCTUATION && continue
            markiterbinding!(x[1][i])
        end
    elseif typof(x) === CSTParser.Do
        if typof(x[3]) === CSTParser.TupleH
            for i in 1:length(x[3])
                typof(x[3][i]) === PUNCTUATION && continue
                mark_binding!(x[3][i])
            end
        end
    elseif typof(x) === FunctionDef
        name = CSTParser.get_name(x)
        # mark external binding
        x.meta.binding = Binding(name, x, CoreTypes.Function, [], nothing, nothing)
        if typof(name) === IDENTIFIER
            setref!(name, bindingof(x))
        end
        mark_sig_args!(CSTParser.get_sig(x))
    elseif typof(x) === ModuleH || typof(x) === BareModule
        x.meta.binding = Binding(x[2], x, CoreTypes.Module, [], nothing, nothing)
        setref!(x[2], bindingof(x))
    elseif typof(x) === Macro
        name = CSTParser.get_name(x)
        x.meta.binding = Binding(name, x, CoreTypes.Function, [], nothing, nothing)
        if typof(name) === IDENTIFIER
            setref!(name, bindingof(x))
        end
        mark_sig_args!(CSTParser.get_sig(x))
    elseif typof(x) === CSTParser.Try && length(x) > 3
        mark_binding!(x[4])
    elseif typof(x) === CSTParser.Abstract || typof(x) === CSTParser.Primitive
        name = CSTParser.get_name(x)
        x.meta.binding = Binding(name, x, CoreTypes.DataType, [], nothing, nothing)
        if typof(name) === IDENTIFIER
            setref!(name, bindingof(x))
        end
        mark_parameters(CSTParser.get_sig(x))
    elseif typof(x) === CSTParser.Mutable || typof(x) === CSTParser.Struct
        name = CSTParser.get_name(x)
        x.meta.binding = Binding(name, x, CoreTypes.DataType, [], nothing, nothing)
        if typof(name) === IDENTIFIER
            setref!(name, bindingof(x))
        end
        mark_parameters(CSTParser.get_sig(x))
        blocki = typof(x[3]) === CSTParser.Block ? 3 : 4
        for i in 1:length(x[blocki])
            CSTParser.defines_function(x[blocki][i]) && continue
            mark_binding!(x[blocki][i])
        end
    elseif typof(x) === CSTParser.Local
        if length(x) == 2
            if typof(x[2]) === CSTParser.IDENTIFIER
                mark_binding!(x[2])
            elseif typof(x[2]) === CSTParser.TupleH
                for i = 1:length(x[2])
                    if typof(x[2][i]) === CSTParser.IDENTIFIER
                        mark_binding!(x[2][i])
                    end
                end
            end
        end

    end
end


function mark_binding!(x::EXPR, val = x)
    if typof(x) === CSTParser.Kw
        mark_binding!(x[1], x)
    elseif typof(x) === CSTParser.TupleH || typof(x) === Parameters
        for arg in x
            typof(arg) === PUNCTUATION && continue
            mark_binding!(arg, val)
        end
    elseif typof(x) === CSTParser.BinaryOpCall && kindof(x[2]) === CSTParser.Tokens.DECLARATION && typof(x[1]) === CSTParser.TupleH
        mark_binding!(x[1], x)
    elseif typof(x) === CSTParser.InvisBrackets
        mark_binding!(CSTParser.rem_invis(x), val)
    elseif typof(x) == UnaryOpCall && kindof(x[1]) === CSTParser.Tokens.DECLARATION
        return x
    else
        if !hasmeta(x)
            x.meta = Meta()
        end
        x.meta.binding = Binding(CSTParser.get_name(x), val, nothing, [], nothing, nothing)
    end
    return x
end


function mark_parameters(sig::EXPR)
    signame = CSTParser.rem_where_subtype(sig)
    if typof(signame) === CSTParser.Curly
        for i = 3:length(signame) - 1
            if typof(signame[i]) !== PUNCTUATION
                mark_binding!(signame[i])
            end
        end
    end
    return sig
end


function markiterbinding!(iter::EXPR)
    if typof(iter) === BinaryOpCall && kindof(iter[2]) in (CSTParser.Tokens.EQ, CSTParser.Tokens.IN, CSTParser.Tokens.ELEMENT_OF)
        mark_binding!(iter[1], iter)
    elseif typof(iter) === CSTParser.Block
        for i = 1:length(iter)
            typof(iter[i]) === PUNCTUATION && continue
            markiterbinding!(iter[i])
        end
    end
    return iter
end

function mark_sig_args!(x::EXPR)
    if typof(x) === Call || typof(x) === CSTParser.TupleH
        if typof(x[1]) === CSTParser.InvisBrackets && typof(x[1][2]) === BinaryOpCall && kindof(x[1][2][2]) === CSTParser.Tokens.DECLARATION
            mark_binding!(x[1][2])
        end
        for i = 2:length(x) - 1
            a = x[i]
            if typof(a) === Parameters
                for j = 1:length(a)
                    aa = a[j]
                    if !(typof(aa) === PUNCTUATION)
                        mark_binding!(aa)
                    end
                end
            elseif !(typof(a) === PUNCTUATION)
                mark_binding!(a)
            end
        end
    elseif typof(x) === WhereOpCall
        for i in 3:length(x)
            if !(typof(x[i]) === PUNCTUATION)
                mark_binding!(x[i])
            end
        end
        mark_sig_args!(x[1])
    elseif typof(x) === BinaryOpCall
        if kindof(x[2]) == CSTParser.Tokens.DECLARATION
            mark_sig_args!(x[1])
        else
            mark_binding!(x[1])
            mark_binding!(x[3])
        end
    elseif typof(x) == UnaryOpCall && typof(x[2]) == CSTParser.InvisBrackets
        mark_binding!(x[2][2])
    end
end

function mark_typealias_bindings!(x::EXPR)
    mark_binding!(x, x)
    setscope!(x, Scope(x))
    for i = 2:length(x[1])
        if typof(x[1][i]) === IDENTIFIER
            mark_binding!(x[1][i])
        elseif typof(x[1][i]) === BinaryOpCall && kindof(x[1][i][2]) === CSTParser.Tokens.ISSUBTYPE && typof(x[1][i][1]) === IDENTIFIER
            mark_binding!(x[1][i][1])
        end
    end
    return x
end

function _in_func_def(x::EXPR)
    # only called in WhereOpCall
    # check 1st arg contains a call (or op call)
    ex = x[1]
    while true
        if typof(ex) === WhereOpCall || (typof(ex) === BinaryOpCall && kindof(ex[2]) === CSTParser.Tokens.DECLARATION)
            ex = ex[1]
        elseif typof(ex) === Call || (typof(ex) === BinaryOpCall && kindof(ex[2]) !== CSTParser.Tokens.DOT) || typof(ex) == CSTParser.UnaryOpCall
            break
        else
            return false
        end
    end
    # check parent is func def
    ex = x
    while true
        if !(parentof(ex) isa EXPR)
            return false
        elseif typof(parentof(ex)) === WhereOpCall || typof(parentof(ex)) === CSTParser.InvisBrackets
            ex = parentof(ex)
        elseif typof(parentof(ex)) === FunctionDef || CSTParser.is_assignment(parentof(ex))
            return true
        else
            return false
        end
    end
    return false
end

function add_binding(x, state, scope = state.scope)
    if bindingof(x) isa Binding
        bindingof(x).prev = nothing
        bindingof(x).next = nothing
        if typof(bindingof(x).name) === CSTParser.IDENTIFIER
            name = valof(bindingof(x).name)
        elseif typof(bindingof(x).name) === CSTParser.NONSTDIDENTIFIER
            name = valof(bindingof(x).name[2])
        elseif CSTParser.typof(bindingof(x).name) === CSTParser.MacroName
            name = string(Expr(bindingof(x).name))
        elseif CSTParser.typof(bindingof(x).name) === CSTParser.OPERATOR
            name = string(Expr(bindingof(x).name))
        else
            return
        end
        # check for global marker
        if isglobal(name, scope)
            scope = _get_global_scope(state.scope)
        end

        if typof(x) === Macro
            scope.names[string("@", name)] = bindingof(x)
            mn = CSTParser.get_name(x)
            if typof(mn) === IDENTIFIER
                setref!(mn, bindingof(x))
            end
        else
            if scopehasbinding(scope, name)
                bindingof(x).prev = scope.names[name]
                scope.names[name] = bindingof(x)
                bindingof(x).prev.next = bindingof(x)
            else
                # Checks for bindings which overwrite other module's bindings
                if typof(parentof(bindingof(x).name)) === CSTParser.Quotenode && typof(parentof(parentof(bindingof(x).name))) === BinaryOpCall && typof(parentof(parentof(bindingof(x).name))[1]) === IDENTIFIER # Only checks 1 level (e.g. M.name)
                    s1 = scope
                    while true
                        if s1.modules !== nothing
                            if scopehasmodule(s1, Symbol(valof(parentof(parentof(bindingof(x).name))[1]))) # this scope (s1) has a module with matching name
                                mod = getscopemodule(s1, Symbol(valof(parentof(parentof(bindingof(x).name))[1])))
                                if mod isa SymbolServer.ModuleStore && haskey(mod, Symbol(name))
                                    bindingof(x).prev = mod[Symbol(name)]
                                end
                            end
                            break # We've reached a scope that loads modules, no need to keep searching upwards
                        end
                        if parentof(s1) === nothing
                            break
                        else
                            s1 = parentof(s1)
                        end
                    end
                end
                scope.names[name] = bindingof(x)
            end
        end
        infer_type(bindingof(x), scope, state)
    elseif bindingof(x) isa SymbolServer.SymStore
        scope.names[valof(x)] = bindingof(x)
    end
end

isglobal(name, scope) = false
isglobal(name::String, scope) = scopehasbinding(scope, "#globals") && name in scope.names["#globals"].refs

function mark_globals(x::EXPR, state)
    if typof(x) === CSTParser.Global
        if !scopehasbinding(state.scope, "#globals")
            state.scope.names["#globals"] = Binding(EXPR(IDENTIFIER, EXPR[], 0, 0, "#globals", CSTParser.NoKind, false, nothing, nothing), nothing, nothing, [], nothing, nothing)
        end
        for i = 2:length(x)
            if typof(x[i]) === CSTParser.IDENTIFIER && !scopehasbinding(state.scope, valof(x[i]))
                push!(state.scope.names["#globals"].refs, valof(x[i]))
            end
        end

    end
end
