module StaticLint
const loaded_mods = Dict{String,Tuple{Set{Symbol},Set{Symbol}}}()
using CSTParser
const BaseCoreNames = Set(vcat(names(Base), names(Core), :end, :new, :ccall))

mutable struct File
    path::String
    parent::Union{Void,Tuple{File,UnitRange{Int}}}
    children::Vector{File}
end

mutable struct Location{T}
    path::String
    offset::T
end

mutable struct Binding
    t
    loc::Location{UnitRange{Int}}
    val
end

mutable struct Scope
    t::String
    namespace::String
    parent::Union{Void,Scope}
    children::Vector{Scope}
    names::Dict{String,Vector{Binding}}
    range::UnitRange{Int64}
    loc::Location
end
Scope() = Scope("__toplevel__", "", nothing, [], Dict(), 1:typemax(Int), Location("", 1:typemax(Int)))
function Base.display(s::Scope, i = 0)
    println(" "^i, s.t, ":[", join(keys(s.names), ", "), "]")
    for c in s.children
        display(c, i + 1)
    end
end

struct MissingBinding
    s::Scope
end
mutable struct Reference{T}
    x::T
    b::Union{Binding,MissingBinding}
    loc::Location{UnitRange{Int}}
end


struct FileSystem end
mutable struct State{T}
    current_scope::Scope
    loc::Location
    target_file::String
    bad_refs::Vector{Reference}
    refs::Vector{Reference}
    nodecl::UnitRange{Int}
    isquotenode::Bool
    includes::Dict
    fs::T
end
State(s) = State{FileSystem}(s, Location("", 0), "", [], [], 0:0, false, Dict(), FileSystem())
State() = State(Scope())


function add_binding(x, name, t, S::State, offset)
    if haskey(S.current_scope.names, name)
        push!(S.current_scope.names[name], Binding(t, Location(S.loc.path, offset), x))
    else
        S.current_scope.names[name] = Binding[Binding(t, Location(S.loc.path, offset), x)]
    end
end

function add_scope(a, s, S::State, t, name = "")
    push!(S.current_scope.children, Scope(t, name, s, [], Dict(), S.loc.offset + a.span, Location(S.loc.path, S.loc.offset + a.span)))
    S.current_scope = last(S.current_scope.children)
end


function create_scope(x, s, S::State)
    if CSTParser.defines_module(x)
        add_scope(x, s, S, "Module", CSTParser.str_value(CSTParser.get_name(x)))
    elseif CSTParser.defines_function(x)
        add_scope(x, s, S, "Function")
        sig = CSTParser.get_sig(x)
        for param in CSTParser.get_sig_params(sig)
            add_binding(sig, param, :DataType, S, S.loc.offset + x.span)
        end
        for arg in CSTParser.get_args(x)
            add_binding(arg, CSTParser.str_value(arg), :Any, S, S.loc.offset + x.span)
        end
    elseif CSTParser.defines_macro(x)
        add_scope(x, s, S, "Macro")
        for arg in CSTParser.get_args(x)
            add_binding(arg, CSTParser.str_value(arg), :Any, S, S.loc.offset + x.args[1].fullspan + x.args[2].span)
        end
    elseif CSTParser.defines_datatype(x)
        add_scope(x, s, S, string(typeof(x).parameters[1].name.name))
        if x isa CSTParser.EXPR{CSTParser.Struct} || x isa CSTParser.EXPR{CSTParser.Mutable}
            sig = CSTParser.get_sig(x)
            sig = CSTParser.rem_subtype(sig)
            sig = CSTParser.rem_where(sig)
            for arg in CSTParser.get_curly_params(sig)
                add_binding(sig, arg, :Any, S, S.loc.offset + x.args[1].fullspan + x.args[1].span)
            end
            
            for arg in CSTParser.get_args(x)
                add_binding(arg, CSTParser.str_value(arg), :Any, S, S.loc.offset + x.span)
            end
        end
    elseif x isa CSTParser.EXPR{CSTParser.Let}
        add_scope(x, s, S, "Let")
    elseif x isa CSTParser.EXPR{CSTParser.Do}
        add_scope(x, s, S, "Do") 
        for arg in CSTParser.get_args(x)
            add_binding(arg, CSTParser.str_value(arg), :Any, S, S.loc.offset + x.args[1].fullspan + x.args[2].fullspan + x.args[3].span)
        end
    elseif x isa CSTParser.EXPR{CSTParser.While}
        add_scope(x, s, S, "While") 
    elseif x isa CSTParser.EXPR{CSTParser.For}
        add_scope(x, s, S, "For")
        S.nodecl = S.loc.offset + x.args[1].fullspan + x.args[2].span
        if x.args[2] isa CSTParser.EXPR{CSTParser.Block}
            offset1 = S.loc.offset + x.args[1].fullspan
            for iter in x.args[2]
                if CSTParser.is_valid_iterator(iter)
                    if iter.arg1 isa CSTParser.IDENTIFIER || iter.arg1 isa CSTParser.EXPR{CSTParser.TupleH}
                        for ass in CSTParser.flatten_tuple(iter.arg1)
                            add_binding(ass, CSTParser.str_value(ass), :Any, S, offset1 + iter.span)
                        end
                    end
                end
                offset1 += iter.fullspan
            end
        elseif CSTParser.is_valid_iterator(x.args[2])
            offset1 = S.loc.offset + x.args[1].fullspan
            if x.args[2].arg1 isa CSTParser.IDENTIFIER || x.args[2].arg1 isa CSTParser.EXPR{CSTParser.TupleH}
                for ass in CSTParser.flatten_tuple(x.args[2].arg1)
                    add_binding(ass, CSTParser.str_value(ass), :Any, S, offset1 + x.args[2].span)
                end
            end
        end
    elseif x isa CSTParser.EXPR{CSTParser.Try} 
        add_scope(x, s, S, "Try")
    elseif x isa CSTParser.WhereOpCall
        add_scope(x, s, S, "WhereOpCall")
        for arg in CSTParser.get_where_params(x)
            add_binding(x, arg, :DataType, S, S.loc.offset + x.span)
        end
    elseif x isa CSTParser.EXPR{CSTParser.Generator}
        add_scope(x, s, S, "Generator") 
        for arg in CSTParser.get_args(x)
            add_binding(arg, CSTParser.str_value(arg), :Any, S, S.loc.offset + x.args[1].fullspan + x.args[2].fullspan + x.args[3].span)
        end
    elseif CSTParser.defines_anon_function(x)
        add_scope(x, s, S, "anon_func")
        for arg in CSTParser.get_args(x)
            add_binding(arg, CSTParser.str_value(arg), :Any, S, S.loc.offset + x.span)
        end
    elseif CSTParser.is_assignment(x) && x.arg1 isa CSTParser.EXPR{CSTParser.Curly}
        add_scope(x, s, S, "Typealias") 
        for param in CSTParser.get_curly_params(x.arg1)
            add_binding(x, param, :Any, S, S.loc.offset + x.span)
        end
    end
end

function get_rhs(x)
    if CSTParser.is_assignment(x.arg2)
        return get_rhs(x.arg2)
    else
        return x.arg2
    end
end

function get_external_binding(x, s, S::State)
    if (S.loc.offset + x.span) in S.nodecl
        return false
    elseif CSTParser.defines_function(x)
        name = CSTParser.str_value(CSTParser.get_name(x))
        add_binding(x, name, :Function, S, S.loc.offset + x.span)
        return true
    elseif CSTParser.defines_macro(x)
        name = CSTParser.str_value(CSTParser.get_name(x))
        add_binding(x, name, :Macro, S, S.loc.offset + x.span)
        return true
    elseif CSTParser.defines_datatype(x)
        name = CSTParser.str_value(CSTParser.get_name(x))
        add_binding(x, name, :DataType, S, S.loc.offset + x.span)
        return true
    elseif CSTParser.defines_module(x)
        name = CSTParser.str_value(CSTParser.get_name(x))
        add_binding(x, name, :Module, S, S.loc.offset + x.span)
        return false
    elseif CSTParser.is_assignment(x) 
        ass = x.arg1
        ass = CSTParser.rem_decl(ass)
        ass = CSTParser.rem_curly(ass)
        if ass isa CSTParser.IDENTIFIER
            add_binding(x, CSTParser.str_value(ass), :Any, S, S.loc.offset + x.span)
        elseif ass isa CSTParser.EXPR{CSTParser.TupleH}
            for arg in CSTParser.flatten_tuple(ass)
                add_binding(x, CSTParser.str_value(arg), :Any, S, S.loc.offset + x.span)
            end
        end
        return true
    elseif x isa CSTParser.EXPR{CSTParser.Local} && !CSTParser.is_assignment(x.args[1])
        if x.args[2] isa CSTParser.IDENTIFIER
            add_binding(x, CSTParser.str_value(x.args[2]), :Any, S, S.loc.offset + x.span)
        else
            for arg in x.args[2]
                if arg isa CSTParser.IDENTIFIER
                    add_binding(arg, CSTParser.str_value(arg), :Any, S, S.loc.offset + x.span)
                end
            end
        end
        return true
    elseif x isa CSTParser.EXPR{CSTParser.MacroCall}
        if x.args[1] isa CSTParser.EXPR{CSTParser.MacroName} && length(x.args[1].args) == 2 && CSTParser.str_value(x.args[1].args[2]) == "enum"
            enum_name = ""
            for i = 2:length(x.args)
                arg = x.args[i]
                if arg isa CSTParser.IDENTIFIER
                    if isempty(enum_name)
                        enum_name = CSTParser.str_value(arg)
                        add_binding(x, enum_name, :DataType, S, S.loc.offset + x.span)
                    else
                        add_binding(x, CSTParser.str_value(arg), Symbol(enum_name), S, S.loc.offset + x.span)
                    end
                end
            end
        end
        return true
    elseif x isa CSTParser.EXPR{T} where T <: Union{CSTParser.Import,CSTParser.Using,CSTParser.ImportAll}
        get_imports(x, S)
        return true
    end
    return false
end

find_ref(name, S::State) = find_ref(name, S.current_scope, S)

function find_ref(name, s, S::State)
    if name in keys(s.names)
        return last(s.names[name])
    elseif s.parent != nothing
        return find_ref(name, s.parent, S)
    else
        if Symbol(name) in BaseCoreNames
            return Binding("BaseCore", Location("____", 0:0), nothing)
        else
            return MissingBinding(S.current_scope)
        end
    end
end

# Build scopes


function lint_call(x, s, S) end
function lint_call(x::CSTParser.EXPR{CSTParser.Call}, s, S)
    fname = CSTParser.get_name(x)
    if CSTParser.str_value(fname) == "include"
        follow_include(x, s, S)
    end

end

Base.in(x::UnitRange{Int}, y::UnitRange{Int}) = first(x) ≥ first(y) && last(x) ≤ last(y)

function find_bad_refs(S)
    for r in S.refs
        if r.b isa StaticLint.MissingBinding
            resolved = resolve_missing_binding(r)
            if !resolved
                push!(S.bad_refs, r)
            end
        end
    end
end


function resolve_missing_binding(r::Reference, s = r.b.s)
    if CSTParser.str_value(r.x) in keys(s.names)
        r.b = last(s.names[CSTParser.str_value(r.x)])
        return true
    elseif s.parent != nothing
        return resolve_missing_binding(r, s.parent)
    end
    return false
end


include("trav.jl")
include("imports.jl")
include("includes.jl")
mod_names(Main, loaded_mods)
end # module
