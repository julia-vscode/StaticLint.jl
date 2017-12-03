module StaticLint

using CSTParser

const BaseCoreNames = Set(vcat(names(Base), names(Core), :end, :new, :ccall))

mutable struct Binding
    t
    offset::UnitRange{Int}
    index::Int
end

mutable struct Scope
    t::String
    namespace::String
    parent::Union{Void,Scope}
    children::Vector{Scope}
    names::Dict{String,Binding}
    range::UnitRange{Int64}
    n::Int
end
Scope() = Scope("__toplevel__", "", nothing, [], Dict(), 1:typemax(Int), 0)
function Base.display(s::Scope, i = 0)
    println(" "^i, s.t, ":[", join(keys(s.names), ", "), "]")
    for c in s.children
        display(c, i + 1)
    end
end


mutable struct State
    current_scope::Scope
    offset::Int
    ids::Vector{Tuple{UnitRange{Int},String}}
    bad_refs::Vector{Binding}
    nodecl::UnitRange{Int}
end
State(s) = State(s, 0, [], [], 0:0)
State() = State(Scope())

function add_binding(name, t, S, offset)
    S.current_scope.n += 1
    S.current_scope.names[name] = Binding(t, offset, S.current_scope.n)
end

function add_scope(a, s, S, t, name = "")
    push!(S.current_scope.children, Scope(t, name, s, [], Dict(), S.offset + a.span, 0))
    S.current_scope = last(S.current_scope.children)
end


function create_scope(x, s, S)
    if CSTParser.defines_module(x)
        add_scope(x, s, S, "Module", CSTParser.str_value(CSTParser.get_name(x)))
    elseif CSTParser.defines_function(x)
        add_scope(x, s, S, "Function")
        for param in CSTParser.get_sig_params(CSTParser.get_sig(x))
            add_binding(param, :DataType, S, S.offset + x.span)
        end
        for arg in CSTParser.get_args(x)
            add_binding(CSTParser.str_value(arg), :Any, S, S.offset + x.span)
        end
    elseif CSTParser.defines_macro(x)
        add_scope(x, s, S, "Macro")
        for arg in CSTParser.get_args(x)
            add_binding(CSTParser.str_value(arg), :Any, S, S.offset + x.args[2].span)
        end
    elseif CSTParser.defines_datatype(x)
        add_scope(x, s, S, string(typeof(x).parameters[1].name.name))
        if x isa CSTParser.EXPR{CSTParser.Struct} || x isa CSTParser.EXPR{CSTParser.Mutable}
            for arg in CSTParser.get_args(x)
                add_binding(CSTParser.str_value(arg), :Any, S, S.offset + x.span)
            end
        end
    elseif x isa CSTParser.EXPR{CSTParser.Let}
        add_scope(x, s, S, "Let")
    elseif x isa CSTParser.EXPR{CSTParser.Do}
        add_scope(x, s, S, "Do") 
    elseif x isa CSTParser.EXPR{CSTParser.While}
        add_scope(x, s, S, "While") 
    elseif x isa CSTParser.EXPR{CSTParser.For}
        add_scope(x, s, S, "For")
    elseif x isa CSTParser.EXPR{CSTParser.Try} 
        add_scope(x, s, S, "Try")
    elseif x isa CSTParser.WhereOpCall
        add_scope(x, s, S, "WhereOpCall")
        for arg in CSTParser.get_where_params(x)
            add_binding(arg, :DataType, S, S.offset + x.span)
        end
    elseif x isa CSTParser.EXPR{CSTParser.Generator}
        add_scope(x, s, S, "Generator") 
    elseif CSTParser.defines_anon_function(x)
        add_scope(x, s, S, "anon_func")
        for arg in CSTParser.get_args(x)
            add_binding(CSTParser.str_value(arg), :Any, S, S.offset + x.span)
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

function get_external_binding(x, s, S)
    if (S.offset + x.span) in S.nodecl
        return
    elseif CSTParser.defines_function(x)
        name = CSTParser.str_value(CSTParser.get_name(x))
        add_binding(name, :Function, S, S.offset + x.span)
    elseif CSTParser.defines_macro(x)
        name = CSTParser.str_value(CSTParser.get_name(x))
        add_binding(name, :Macro, S, S.offset + x.span)
    elseif CSTParser.defines_datatype(x)
        name = CSTParser.str_value(CSTParser.get_name(x))
        add_binding(name, :DataType, S, S.offset + x.span)
    elseif CSTParser.defines_module(x)
        name = CSTParser.str_value(CSTParser.get_name(x))
        add_binding(name, :Module, S, S.offset + x.span)
    elseif CSTParser.is_assignment(x) 
        if x.arg1 isa CSTParser.IDENTIFIER
            add_binding(CSTParser.str_value(x.arg1), :Any, S, S.offset + x.span)
        end
    elseif x isa CSTParser.EXPR{CSTParser.Local} && !CSTParser.is_assignment(x.args[1])
        if x.args[2] isa CSTParser.IDENTIFIER
            add_binding(CSTParser.str_value(x.args[2]), :Any, S, S.offset + x.span)
        else
            for arg in x.args[2]
                if arg isa CSTParser.IDENTIFIER
                    add_binding(CSTParser.str_value(arg), :Any, S, S.offset + x.span)
                end
            end
        end
    end
end

function find_ref(name, S)
    if Symbol(name) in BaseCoreNames
        return Binding("BaseCore", 0:0, -1)
    else
        return find_ref(name, S.current_scope, S)
    end
end

function find_ref(name, s, S)
    if name in keys(s.names)
        return s.names[name]
    elseif s.parent != nothing
        find_ref(name, s.parent, S)
    else
        return Binding(nothing, 0:0, -1)
    end
end

# Build scopes
function trav(x::CSTParser.LeafNode, s, S)
    if x isa CSTParser.IDENTIFIER
        # push!(S.ids, (S.offset + x.span, CSTParser.str_value(x)))
        binding = find_ref(CSTParser.str_value(x), S)
        if binding.t == nothing
            binding.offset = S.offset + x.span
            push!(S.bad_refs, binding)
        else
        end
    end
    S.offset += x.fullspan
end

function trav(x, s, S)
    for a in x
        get_external_binding(a, s, S)
        create_scope(a, s, S)
        trav(a, S.current_scope, S)
        S.current_scope = s
    end
    s
end

function trav(x)
    S = State()
    trav(x, S.current_scope, S)
    return S
end

Base.in(x::UnitRange{Int}, y::UnitRange{Int}) = first(x) ≥ first(y) && last(x) ≤ last(y)
    


function build_namespace(loc, s, names = Dict())
    if loc in s.range
        if s.t == "__toplevel__"
            for (k,b) in s.names
                names[k] = b
            end
        else
            for (k,b) in s.names
                if b.offset < loc
                    names[k] = b
                end
            end
        end
        for c in s.children
            if loc in c.range
                build_namespace(loc, c, names)
            end
        end
    end
    
    return names    
end

end # module
