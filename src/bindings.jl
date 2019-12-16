mutable struct Binding
    name::EXPR
    val::Union{Binding,EXPR,SymbolServer.SymStore,Nothing}
    type::Union{Binding,EXPR,SymbolServer.SymStore,Nothing}
    refs
    prev::Union{Binding,SymbolServer.SymStore,Nothing}
    next::Union{Binding,SymbolServer.SymStore,Nothing}
end
Binding(x::EXPR) = Binding(CSTParser.get_name(x), x, nothing, nothing, nothing, nothing)

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



function mark_bindings!(x::EXPR, state)
    if hasbinding(x)
        return
    end
    if !hasmeta(x)
        x.meta = Meta()
    end
    if typof(x) === BinaryOpCall
        if kindof(x.args[2]) === CSTParser.Tokens.EQ
            if CSTParser.is_func_call(x.args[1])
                name = CSTParser.get_name(x.args[1])
                mark_binding!(x)
                mark_sig_args!(x.args[1])
            elseif typof(x.args[1]) === CSTParser.Curly
                mark_typealias_bindings!(x)
            else
                mark_binding!(x.args[1], x)
            end
        elseif kindof(x.args[2]) === CSTParser.Tokens.ANON_FUNC
            mark_binding!(x.args[1], x)
        end
    elseif typof(x) === WhereOpCall
        for i = 3:length(x.args)
            typof(x.args[i]) === PUNCTUATION && continue
            mark_binding!(x.args[i])
        end
    elseif typof(x) === CSTParser.For
        markiterbinding!(x.args[2])
    elseif typof(x) === CSTParser.Generator
        for i = 3:length(x.args)
            typof(x.args[i]) === PUNCTUATION && continue
            markiterbinding!(x.args[i])
        end
    elseif typof(x) === CSTParser.Filter
        for i = 1:length(x.args)-2
            typof(x.args[i]) === PUNCTUATION && continue
            markiterbinding!(x.args[i])
        end
    elseif typof(x) === CSTParser.Do
        if typof(x.args[3]) === CSTParser.TupleH
            for i in 1:length(x.args[3].args)
                typof(x.args[3].args[i]) === PUNCTUATION && continue
                mark_binding!(x.args[3].args[i])
            end
        end
        # markiterbinding!(x.args[3])
    elseif typof(x) === FunctionDef
        name = CSTParser.get_name(x)
        # mark external binding
        x.meta.binding = Binding(name, x, CoreTypes.Function, [], nothing, nothing)
        if typof(name) === IDENTIFIER
            setref!(name, bindingof(x))
        end
        mark_sig_args!(CSTParser.get_sig(x))
    elseif typof(x) === ModuleH || typof(x) === BareModule
        x.meta.binding = Binding(x.args[2], x, CoreTypes.Module, [], nothing, nothing)
        setref!(x.args[2], bindingof(x))
    elseif typof(x) === Macro
        name = CSTParser.get_name(x)
        x.meta.binding = Binding(name, x, CoreTypes.Function, [], nothing, nothing)
        if typof(name) === IDENTIFIER
            setref!(name, bindingof(x))
        end
        mark_sig_args!(CSTParser.get_sig(x))
    elseif typof(x) === CSTParser.Try && length(x.args) > 3 
        mark_binding!(x.args[4])
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
        blocki = typof(x.args[3]) === CSTParser.Block ? 3 : 4
        for i in 1:length(x.args[blocki])
            CSTParser.defines_function(x.args[blocki].args[i]) && continue
            mark_binding!(x.args[blocki].args[i])
        end
    end
end


function mark_binding!(x::EXPR, val = x)
    if typof(x) === CSTParser.Kw
        mark_binding!(x.args[1], x)
    elseif typof(x) === CSTParser.TupleH || typof(x) === Parameters
        for arg in x.args
            typof(arg) === PUNCTUATION && continue    
            mark_binding!(arg, val)
        end
    elseif typof(x) === CSTParser.BinaryOpCall && kindof(x.args[2]) === CSTParser.Tokens.DECLARATION && typof(x.args[1]) === CSTParser.TupleH
        mark_binding!(x.args[1], x)
    elseif typof(x) === CSTParser.InvisBrackets
        mark_binding!(CSTParser.rem_invis(x), val)
    elseif typof(x) == UnaryOpCall && kindof(x.args[1]) === CSTParser.Tokens.DECLARATION
        return x
    else#if typof(x) === IDENTIFIER || (typof(x) === BinaryOpCall && kindof(x.args[2]) === CSTParser.Tokens.DECLARATION)
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
        for i = 3:length(signame.args) - 1
            if typof(signame.args[i]) !== PUNCTUATION
                mark_binding!(signame.args[i])
            end
        end
    end
    return sig
end


function markiterbinding!(iter::EXPR)
    if typof(iter) === BinaryOpCall && kindof(iter.args[2]) in (CSTParser.Tokens.EQ, CSTParser.Tokens.IN, CSTParser.Tokens.ELEMENT_OF)
        mark_binding!(iter.args[1], iter)
    elseif typof(iter) === CSTParser.Block
        for i = 1:length(iter.args)
            typof(iter.args[i]) === PUNCTUATION && continue
            markiterbinding!(iter.args[i])
        end
    end
    return iter
end

function mark_sig_args!(x::EXPR)
    if typof(x) === Call || typof(x) === CSTParser.TupleH
        if typof(x.args[1]) === CSTParser.InvisBrackets && typof(x.args[1].args[2]) === BinaryOpCall && kindof(x.args[1].args[2].args[2]) === CSTParser.Tokens.DECLARATION
            mark_binding!(x.args[1].args[2])
        end
        for i = 2:length(x.args) - 1
            a = x.args[i]
            if typof(a) === Parameters
                for j = 1:length(a.args)
                    aa = a.args[j]
                    if !(typof(aa) === PUNCTUATION)
                        mark_binding!(aa)
                    end
                end
            elseif !(typof(a) === PUNCTUATION)
                mark_binding!(a)
            end
        end
    elseif typof(x) === WhereOpCall
        for i in 3:length(x.args)
            if !(typof(x.args[i]) === PUNCTUATION)
                mark_binding!(x.args[i])
            end
        end
        mark_sig_args!(x.args[1])
    elseif typof(x) === BinaryOpCall
        if kindof(x.args[2]) == CSTParser.Tokens.DECLARATION
            mark_sig_args!(x.args[1])
        else
            mark_binding!(x.args[1])
            mark_binding!(x.args[3])
        end
    elseif typof(x) == UnaryOpCall && typof(x.args[2]) == CSTParser.InvisBrackets
        mark_binding!(x.args[2].args[2])
    end
end

function mark_typealias_bindings!(x::EXPR)
    mark_binding!(x, x)
    setscope!(x, Scope(x))
    for i = 2:length(x.args[1].args)
        if typof(x.args[1].args[i]) === IDENTIFIER
            mark_binding!(x.args[1].args[i])
        elseif typof(x.args[1].args[i]) === BinaryOpCall && kindof(x.args[1].args[i].args[2]) === CSTParser.Tokens.ISSUBTYPE && typof(x.args[1].args[i].args[1]) === IDENTIFIER
            mark_binding!(x.args[1].args[i].args[1])
        end
    end
    return x
end

function _in_func_def(x::EXPR)
    # only called in WhereOpCall
    
    # check 1st arg contains a call (or op call)
    ex = x.args[1]
    while true
        if typof(ex) === WhereOpCall || (typof(ex) === BinaryOpCall && kindof(ex.args[2]) === CSTParser.Tokens.DECLARATION)
            ex = ex.args[1]
        elseif typof(ex) === Call || (typof(ex) === BinaryOpCall && !(kindof(ex.args[2]) === CSTParser.Tokens.DOT))
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
        elseif typof(parentof(ex)) === FunctionDef || (typof(parentof(ex)) === BinaryOpCall && kindof(parentof(ex).args[2]) === CSTParser.Tokens.EQ)
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
        elseif CSTParser.typof(bindingof(x).name) === CSTParser.MacroName
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
            if haskey(scope.names, name)
                bindingof(x).prev = scope.names[name]
                scope.names[name] = bindingof(x)
                bindingof(x).prev.next = bindingof(x)
            else
                # Checks for bindings which overwrite other module's bindings
                if typof(parentof(bindingof(x).name)) === CSTParser.Quotenode && typof(parentof(parentof(bindingof(x).name))) === BinaryOpCall && typof(parentof(parentof(bindingof(x).name))[1]) === IDENTIFIER # Only checks 1 level (e.g. M.name)
                    s1 = scope
                    while true
                        if s1.modules !== nothing
                            if haskey(s1.modules, valof(parentof(parentof(bindingof(x).name))[1])) # this scope (s1) has a module with matching name
                                # haskey(s1.modules[valof(parentof(parentof(bindingof(x).name))[1])].vals, name)
                                mod = s1.modules[valof(parentof(parentof(bindingof(x).name))[1])]
                                if mod isa SymbolServer.ModuleStore && haskey(mod.vals, name)
                                    bindingof(x).prev = mod.vals[name]
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
isglobal(name::String, scope) = haskey(scope.names, "#globals") && name in scope.names["#globals"].refs

function mark_globals(x, state)
    if typof(x) === CSTParser.Global
        if !haskey(state.scope.names, "#globals")
            
            state.scope.names["#globals"] = Binding(EXPR(IDENTIFIER,EXPR[], 0, 0, "#globals", CSTParser.NoKind, false, nothing, nothing), nothing, nothing, String[], nothing, nothing)
        end
        if x.args isa Vector{EXPR}
            for i = 2:length(x.args)
                if typof(x.args[i]) === CSTParser.IDENTIFIER && !haskey(state.scope.names, valof(x.args[i]))
                    push!(state.scope.names["#globals"].refs, valof(x.args[i]))
                end
            end
        end
    end
end