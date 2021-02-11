module StaticLint

include("exception_types.jl")

using SymbolServer, CSTParser

using CSTParser: EXPR, isidentifier, setparent!, valof, headof, hastrivia, parentof, isoperator, ispunctuation
# CST utils
using CSTParser: is_getfield, isassignment, isdeclaration, isbracketed, iskwarg, iscall, iscurly, isunarycall, isunarysyntax, isbinarycall, isbinarysyntax, issplat, defines_function, is_getfield_w_quotenode, iswhere, iskeyword, isstringliteral, isparameters, isnonstdid, istuple
using SymbolServer: VarRef

const noname = EXPR(:noname, nothing, nothing, 0, 0, nothing, nothing, nothing)

baremodule CoreTypes # Convenience
using ..SymbolServer
using Base: ==, @static

const DataType = SymbolServer.stdlibs[:Core][:DataType]
const Function = SymbolServer.stdlibs[:Core][:Function]
const Module = SymbolServer.stdlibs[:Core][:Module]
const String = SymbolServer.stdlibs[:Core][:String]
const Char = SymbolServer.stdlibs[:Core][:Char]
const Symbol = SymbolServer.stdlibs[:Core][:Symbol]
const Int = SymbolServer.stdlibs[:Core][:Int]
const Float64 = SymbolServer.stdlibs[:Core][:Float64]
const Vararg = SymbolServer.FakeTypeName(Core.Vararg)

iscoretype(x, name) = false
iscoretype(x::SymbolServer.VarRef, name) = x isa SymbolServer.DataTypeStore && x.name.name == name && x.name isa SymbolServer.VarRef && x.name.parent.name == :Core
iscoretype(x::SymbolServer.DataTypeStore, name) = x isa SymbolServer.DataTypeStore && x.name.name.name == name && x.name.name isa SymbolServer.VarRef && x.name.name.parent.name == :Core
isdatatype(x) = iscoretype(x, :DataType)
isfunction(x) = iscoretype(x, :Function)
ismodule(x) = iscoretype(x, :Module)
isstring(x) = iscoretype(x, :String)
ischar(x) = iscoretype(x, :Char)
issymbol(x) = iscoretype(x, :Symbol)
isint(x) = iscoretype(x, :Int64)
isfloat(x) = iscoretype(x, :Float64)
isvector(x) = iscoretype(x, :Vector)
isarray(x) = iscoretype(x, :Array)
isva(x::SymbolServer.FakeUnionAll) = isva(x.body)
@static if Core.Vararg isa Core.Type
    function isva(x)
        return (x isa SymbolServer.FakeTypeName && x.name.name == :Vararg &&
            x.name.parent isa SymbolServer.VarRef && x.name.parent.name == :Core)
    end
else
    isva(x) = x isa SymbolServer.FakeTypeofVararg
end
end

const _DataType = SymbolServer.stdlibs[:Core][:DataType]

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
    included_files::Vector{String}
    scope::Scope
    in_modified_expr::Bool
    modified_exprs::Union{Nothing,Vector{EXPR}}
    delayed::Vector{EXPR}
    resolveonly::Vector{EXPR}
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
    
    old_in_modified_expr = state.in_modified_expr
    if state.modified_exprs !== nothing && x in state.modified_exprs
        state.in_modified_expr = true
    end
    if CSTParser.defines_function(x) || CSTParser.defines_macro(x) || headof(x) === :export
        if state.in_modified_expr
            push!(state.delayed, x)
        else
            push!(state.resolveonly, x)
        end
    else
        traverse(x, state)
    end
    
    state.in_modified_expr = old_in_modified_expr
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
    if state.scope != s0
        for (k, b) in state.scope.names
            infer_type_by_use(b, state.server)
        end
        state.scope = s0
    end
    return state.scope
end

mutable struct ResolveOnly <: State
    scope::Scope
    server
end

function (state::ResolveOnly)(x::EXPR)
    if hasscope(x)
        s0 = state.scope
        state.scope = scopeof(x)
    else
        s0 = state.scope
    end
    resolve_ref(x, state)

    traverse(x, state)
    if state.scope != s0
        state.scope = s0
    end
    return state.scope
end


"""
    semantic_pass(file, modified_expr=nothing)

Performs a semantic pass across a project from the entry point `file`. A first pass traverses the top-level scope after which secondary passes handle delayed scopes (e.g. functions). These secondary passes can be, optionally, very light and only seek to resovle references (e.g. link symbols to bindings). This can be done by supplying a list of expressions on which the full secondary pass should be made (`modified_expr`), all others will receive the light-touch version.
"""
function semantic_pass(file, modified_expr=nothing)
    server = file.server
    setscope!(getcst(file), Scope(nothing, getcst(file), Dict(), Dict{Symbol,Any}(:Base => getsymbolserver(server)[:Base], :Core => getsymbolserver(server)[:Core]), nothing))
    state = Toplevel(file, [getpath(file)], scopeof(getcst(file)), modified_expr === nothing, modified_expr, EXPR[], EXPR[], server)
    state(getcst(file))
    for x in state.delayed
        if hasscope(x)
            traverse(x, Delayed(scopeof(x), server)) 
            for (k, b) in scopeof(x).names
                infer_type_by_use(b, state.server)
            end
        else
            traverse(x, Delayed(retrieve_delayed_scope(x), server))
        end
    end
    if state.resolveonly !== nothing
        for x in state.resolveonly
            if hasscope(x)
                traverse(x, ResolveOnly(scopeof(x), server))
            else
                traverse(x, ResolveOnly(retrieve_delayed_scope(x), server))
            end
        end
    end
end

"""
    traverse(x, state)

Iterates across the child nodes of an EXPR in execution order (rather than
storage order) calling `state` on each node.
"""
function traverse(x::EXPR, state)
    if (isassignment(x) && !(CSTParser.is_func_call(x.args[1]) || CSTParser.iscurly(x.args[1]))) || CSTParser.isdeclaration(x)
        state(x.args[2])
        state(x.args[1])
    elseif CSTParser.iswhere(x)
        for i = 2:length(x.args)
            state(x.args[i])
        end
        state(x.args[1])
    elseif headof(x) === :generator || headof(x) === :filter
        @inbounds for i = 2:length(x.args)
            state(x.args[i])
        end
        state(x.args[1])
    elseif headof(x) === :call && length(x.args) > 1 && headof(x.args[2]) === :parameters
        state(x.args[1])
        @inbounds for i = 3:length(x.args)
            state(x.args[i])
        end
        state(x.args[2])
    elseif x.args !== nothing && length(x.args) > 0
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
    if CSTParser.iscall(x) && length(x.args) > 0 && isidentifier(x.args[1]) && valofid(x.args[1]) == "include"

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

"""
    get_path(x::EXPR)

Usually called on the argument to `include` calls, and attempts to determine
the path of the file to be included. Has limited support for `joinpath` calls.
"""
function get_path(x::EXPR, state)
    if CSTParser.iscall(x) && length(x.args) == 2
        parg = x.args[2]
        if CSTParser.isstringliteral(parg)
            path = CSTParser.str_value(parg)
            path = normpath(path)
            Base.containsnul(path) && throw(SLInvalidPath("Couldn't convert '$x' into a valid path. Got '$path'"))
            return path
        elseif CSTParser.ismacrocall(parg) && valof(parg.args[1]) == "@raw_str" && CSTParser.isstringliteral(parg.args[3])
            path = normpath(CSTParser.str_value(parg.args[3]))
            Base.containsnul(path) && throw(SLInvalidPath("Couldn't convert '$x' into a valid path. Got '$path'"))
            return path
        elseif CSTParser.iscall(parg) && isidentifier(parg.args[1]) && valofid(parg.args[1]) == "joinpath"
            path_elements = String[]

            for i = 2:length(parg.args)
                arg = parg[i]
                if _is_macrocall_to_BaseDIR(arg) # Assumes @__DIR__ points to Base macro.
                    push!(path_elements, dirname(getpath(state.file)))
                elseif CSTParser.isstringliteral(arg)
                    push!(path_elements, string(valofid(arg)))
                else
                    return ""
                end
            end
            isempty(path_elements) && return ""

            path = normpath(joinpath(path_elements...))
            Base.containsnul(path) && throw(SLInvalidPath("Couldn't convert '$x' into a valid path. Got '$path'"))
            return path
        end
    end
    return ""
end

include("server.jl")
include("imports.jl")
include("references.jl")
include("macros.jl")
include("linting/checks.jl")
include("type_inf.jl")
include("utils.jl")
include("interface.jl")
end
