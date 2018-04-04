module StaticLint
using CSTParser
include("documentserver.jl")
const Index = Tuple

mutable struct Location
    file::String
    offset::Int
end

mutable struct Binding
    loc::Location
    index::Index
    pos::Int
    val
end

mutable struct Reference{T}
    val::T
    loc::Location
    index::Index
    pos::Int
    delayed::Bool
end

mutable struct Include{T}
    val::T
    file::String
    offset::Int
    index::Index
    pos::Int
end

mutable struct Scope
    parent::Union{Void,Scope}
    children::Vector{Scope}
    offset::UnitRange{Int}
    bindings::Int
    t::DataType
    index::Index
end

Scope() = Scope(nothing, [], 0:-1, 0, CSTParser.TopLevel, ())

mutable struct State
    loc::Location
    bindings::Dict{String,Vector{Binding}}
    refs::Vector{Reference}
    includes::Vector{Include}
    server
end
State() = State(Location("", 0), Dict{String, Vector{Binding}}(), Reference[], Include[], DocumentServer())

function pass(x::CSTParser.LeafNode, state::State, s::Scope, index, blockref, delayed)
    state.loc.offset += x.fullspan
end

function pass(x, state::State, s::Scope, index, blockref, delayed)
    ext_binding(x, state, s, index)
    s1, index1 = create_scope(x, state, s, index)
    if s1.t == CSTParser.FunctionDef || x isa CSTParser.EXPR{CSTParser.Export}
        delayed = true
    end
    if x isa CSTParser.BinarySyntaxOpCall && x.op.kind == CSTParser.Tokens.DECLARATION
        delayed = false
    end
    get_include(x, state, s1, index)
    for a in x
        ablockref = get_ref(a, state, s1, index1, blockref, delayed)
        pass(a, state, s1, index1, ablockref, delayed)
    end
    s
end

include("bindings.jl")
include("references.jl")
include("utils.jl")
include("display.jl")
include("symbolserver.jl")

# SymbolServer.init()
# SymbolServer.load_module(Core, true, true)
end

