module StaticLint
using SymbolServer
using CSTParser
using CSTParser: isidentifier
using CSTParser: EXPR, PUNCTUATION, IDENTIFIER, KEYWORD, OPERATOR
using CSTParser: Call, UnaryOpCall, BinaryOpCall, WhereOpCall, Import, Using, Export, TopLevel, ModuleH, BareModule, Quote, Quotenode, MacroName, MacroCall, Macro, x_Str, FileH, Parameters, FunctionDef
using CSTParser: setparent!, kindof, valof, typof, parentof

const noname = EXPR(CSTParser.NoHead, nothing, 0, 0, nothing, CSTParser.NoKind, false, nothing, nothing)
baremodule CoreTypes # Convenience
using ..SymbolServer
const DataType = SymbolServer.stdlibs["Core"].vals["DataType"]
const Function = SymbolServer.stdlibs["Core"].vals["Function"]
const Module = SymbolServer.stdlibs["Core"].vals["Module"]
const String = SymbolServer.stdlibs["Core"].vals["String"]
const Int = SymbolServer.stdlibs["Core"].vals["Int"]
const Float64 = SymbolServer.stdlibs["Core"].vals["Float64"]

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
    m.ref !== nothing && printstyled(io, " * ", color = :red)
    m.scope !== nothing && printstyled(io, " new scope", color = :green)
    m.error !== nothing && printstyled(io, " lint ", color = :red)
end
hasmeta(x::EXPR) = x.meta isa Meta
hasbinding(m::Meta) = m.binding isa Binding
hasref(m::Meta) = m.ref !== nothing
hasscope(m::Meta) = m.scope isa Scope
scopeof(m::Meta) = m.scope
bindingof(m::Meta) = m.binding

mutable struct State{T}
    file::T
    targetfile::Union{Nothing,T}
    included_files::Vector{String}
    scope::Scope
    delayed::Bool
    urefs::Vector{EXPR}
    server
end

function (state::State)(x::EXPR)
    delayed = state.delayed # store states
    
    resolve_import(x, state)
    if typof(x) === Export # Allow delayed resolution
        state.delayed = true
    end
    mark_bindings!(x, state)
    add_binding(x, state)
    mark_globals(x, state)
    handle_macro(x, state)
    s0 = scopes(x, state)
    resolved = resolve_ref(x, state.scope, state)
    if !resolved && (state.delayed || isglobal(valof(x), state.scope))
        push!(state.urefs, x)
    end
    followinclude(x, state)

    traverse(x, state)

    # return to previous states
    state.scope != s0 && (state.scope = s0)
    state.delayed = delayed
    return state.scope
end

"""
    traverse(x, state)

Iterates across the child nodes of an EXPR in execution order (rather than
storage order) calling `state` on each node.
"""
function traverse(x::EXPR, state)
    if typof(x) === CSTParser.BinaryOpCall && (CSTParser.is_assignment(x) && !CSTParser.is_func_call(x.args[1]) || typof(x.args[2]) === CSTParser.Tokens.DECLARATION) && !(CSTParser.is_assignment(x) && typof(x.args[1]) === CSTParser.Curly)
        state(x.args[3])
        state(x.args[2])
        state(x.args[1])
    elseif typof(x) === CSTParser.WhereOpCall
        @inbounds for i = 3:length(x.args)
            state(x.args[i])
        end
        state(x.args[1])
        state(x.args[2])
    elseif typof(x) === CSTParser.Generator
        @inbounds for i = 2:length(x.args)
            state(x.args[i])
        end
        state(x.args[1])
    elseif typof(x) === CSTParser.Flatten && x.args !== nothing && length(x.args) === 1 && x.args[1].args !== nothing && length(x.args[1]) >= 3 && length(x.args[1].args[1]) >= 3
        for i = 3:length(x.args[1].args[1].args)
            state(x.args[1].args[1].args[i])
        end
        for i = 3:length(x.args[1].args)
            state(x.args[1].args[i])
        end
        state(x.args[1].args[1].args[1])
    elseif x.args !== nothing
        @inbounds for i in 1:length(x.args)
            state(x.args[i])
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
    if typof(x) === Call && typof(x.args[1]) === IDENTIFIER && valof(x.args[1]) == "include"
        path = get_path(x, state)
        if isempty(path)
        elseif hasfile(state.server, path)
        elseif canloadfile(state.server, path)
            loadfile(state.server, path)
        elseif hasfile(state.server, joinpath(dirname(getpath(state.file)), path))
            path = joinpath(dirname(getpath(state.file)), path)
        elseif canloadfile(state.server, joinpath(dirname(getpath(state.file)), path))
            path = joinpath(dirname(getpath(state.file)), path)
            loadfile(state.server, path,)
        else
            path = ""
        end
        if !isempty(path)
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
        else
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
