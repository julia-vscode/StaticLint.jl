module StaticLint

include("exception_types.jl")

using SymbolServer, CSTParser
using CSTParser: EXPR, isidentifier, Import, Using, Export, Quote, Quotenode, x_Str, FunctionDef, setparent!, kindof, valof, typof, parentof, is_assignment, isoperator, ispunctuation, iskw, defines_function
using SymbolServer: VarRef

const noname = EXPR(CSTParser.NoHead, nothing, 0, 0, nothing, CSTParser.NoKind, false, nothing, nothing)
baremodule CoreTypes # Convenience
using ..SymbolServer
using Base: ==
const DataType = SymbolServer.stdlibs[:Core][:DataType]
const Function = SymbolServer.stdlibs[:Core][:Function]
const Module = SymbolServer.stdlibs[:Core][:Module]
const String = SymbolServer.stdlibs[:Core][:String]
const Symbol = SymbolServer.stdlibs[:Core][:Symbol]
const Int = SymbolServer.stdlibs[:Core][:Int]
const Float64 = SymbolServer.stdlibs[:Core][:Float64]
const Vararg = SymbolServer.FakeTypeName(Core.Vararg)
isva(x) = (x isa SymbolServer.FakeTypeName && x.name.name == :Vararg && x.name.parent isa SymbolServer.VarRef && x.name.parent.name == :Core) || (x isa SymbolServer.FakeUnionAll && isva(x.body))
end

include("bindings.jl")
include("scope.jl")

mutable struct Meta
    binding::Union{Nothing,Binding}
    scope::Union{Nothing,Scope}
    ref::Union{Nothing,Binding,SymbolServer.SymStore}
    error
end
Meta() = Meta(nothing, nothing, nothing, nothing)

function Base.show(io::IO, m::Meta)
    m.binding !== nothing && show(io, m.binding)
    m.ref !== nothing && printstyled(io, " * ", color=:red)
    m.scope !== nothing && printstyled(io, " new scope", color=:green)
    m.error !== nothing && printstyled(io, " lint ", color=:red)
end
hasmeta(x::EXPR) = x.meta isa Meta
hasbinding(m::Meta) = m.binding isa Binding
hasref(m::Meta) = m.ref !== nothing
hasscope(m::Meta) = m.scope isa Scope
scopeof(m::Meta) = m.scope
bindingof(m::Meta) = m.binding

abstract type State end
mutable struct Toplevel{T} <: State
    file::T
    targetfile::Union{Nothing,T}
    included_files::Vector{String}
    scope::Scope
    delayed::Vector{EXPR}
    server
end

function (state::Toplevel)(x::EXPR)
    resolve_import(x, state)
    mark_bindings!(x, state)
    add_binding(x, state)
    mark_globals(x, state)
    handle_macro(x, state)
    s0 = scopes(x, state)
    resolve_ref(x, state)
    followinclude(x, state)

    if CSTParser.defines_function(x) || CSTParser.defines_macro(x) || typof(x) === CSTParser.Export
        push!(state.delayed, x)
    else
        traverse(x, state)
    end

    state.scope != s0 && (state.scope = s0)
    return state.scope
end

mutable struct Delayed <: State
    scope::Scope
    server
end

function (state::Delayed)(x::EXPR)
    mark_bindings!(x, state)
    add_binding(x, state)
    mark_globals(x, state)
    handle_macro(x, state)
    s0 = scopes(x, state)
    resolve_ref(x, state)

    traverse(x, state)

    state.scope != s0 && (state.scope = s0)
    return state.scope
end

"""
    traverse(x, state)

Iterates across the child nodes of an EXPR in execution order (rather than
storage order) calling `state` on each node.
"""
function traverse(x::EXPR, state)
    if is_binary_call(x) && (CSTParser.is_assignment(x) && !CSTParser.is_func_call(x[1]) || typof(x[2]) === CSTParser.Tokens.DECLARATION) && !(CSTParser.is_assignment(x) && is_curly(x[1]))
        state(x[3])
        state(x[2])
        state(x[1])
    elseif is_where(x)
        @inbounds for i = 3:length(x)
            state(x[i])
        end
        state(x[1])
        state(x[2])
    elseif typof(x) === CSTParser.Generator
        @inbounds for i = 2:length(x)
            state(x[i])
        end
        state(x[1])
    elseif typof(x) === CSTParser.Flatten  && length(x) === 1 && length(x[1]) >= 3 && length(x[1][1]) >= 3
        for i = 3:length(x[1][1])
            state(x[1][1][i])
        end
        for i = 3:length(x[1])
            state(x[1][i])
        end
        state(x[1][1][1])
    elseif length(x) > 0
        @inbounds for i in 1:length(x)
            state(x[i])
        end
    end
end


"""
    followinclude(x, state)

Checks whether the arguments of a call to `include` can be resolved to a path.
If successful it checks whether a file with that path is loaded on the server  
or a file exists on the disc that can be loaded.
If this is successful it traverses the code associated with the loaded file.

"""
function followinclude(x, state::State)
    if is_call(x) && length(x) > 0 && isidentifier(x[1]) && valofid(x[1]) == "include"
        init_path = path = get_path(x, state)
        if isempty(path)
        elseif isabspath(path)
            if hasfile(state.server, path)
            elseif canloadfile(state.server, path)
                loadfile(state.server, path)
            else
                path = ""
            end
        elseif !isempty(getpath(state.file)) && isabspath(joinpath(dirname(getpath(state.file)), path))
            # Relative path from current
            if hasfile(state.server, joinpath(dirname(getpath(state.file)), path))
                path = joinpath(dirname(getpath(state.file)), path)
            elseif canloadfile(state.server, joinpath(dirname(getpath(state.file)), path))
                path = joinpath(dirname(getpath(state.file)), path)
                loadfile(state.server, path)
            else
                path = ""
            end
        elseif !isempty((basepath = _is_in_basedir(getpath(state.file)); basepath))
            # Special handling for include method used within Base
            path = joinpath(basepath, path)
            if hasfile(state.server, path)
                # skip
            elseif canloadfile(state.server, path)
                loadfile(state.server, path)
            else
                path = ""
            end
        else
            path = ""
        end
        if hasfile(state.server, path)
            if path in state.included_files
                seterror!(x, IncludeLoop)
                return
            end
            oldfile = state.file
            state.file = getfile(state.server, path)
            push!(state.included_files, getpath(state.file))
            setroot(state.file, getroot(oldfile))
            setscope!(getcst(state.file), nothing)
            state(getcst(state.file))
            state.file = oldfile
            pop!(state.included_files)
        elseif !is_in_fexpr(x, CSTParser.defines_function) && !isempty(init_path)
            seterror!(x, MissingFile)
        end
    end
end

include("server.jl")
include("imports.jl")
include("references.jl")
include("macros.jl")
include("linting/checks.jl")
include("type_inf.jl")
include("utils.jl")
end
