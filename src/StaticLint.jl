module StaticLint
using CSTParser, Pkg
const Index = Tuple
struct SIndex
    i::Tuple
    n::Int
end

mutable struct Location
    file::String
    offset::Int
end

include("bindings.jl")

mutable struct Reference{T}
    val::T
    loc::Location
    si::SIndex
    delayed::Bool
end

mutable struct ResolvedRef{T, S}
    r::Reference{T}
    b::S
end

mutable struct Include{T}
    val::T
    file::String
    offset::Int
    index::Index
    pos::Int
end

mutable struct Scope
    parent::Union{Nothing,Scope}
    children::Vector{Scope}
    offset::UnitRange{Int}
    t::DataType
    index::Index
    bindings::Int
end
Scope() = Scope(nothing, [], 0:-1, CSTParser.TopLevel, (), 0)
function Base.display(s::Scope, depth = 0)
    println(" "^depth, "| ", s.t.name.name, " @ ", s.index, " / ", s.offset)
    for a in s.children
        display(a, depth + 1)
    end
end


mutable struct State
    loc::Location
    bindings::Dict{String,Any}
    refs::Vector{Reference}
    includes::Vector{Include}
    server
end
State() = State(Location("", 0), Dict{String, Any}(), Reference[], Include[], DocumentServer())

mutable struct File
    cst::CSTParser.EXPR
    state::State
    scope::Scope
    index::Index
    nb::Int
    parent::String
    rref::Vector{ResolvedRef}
    uref::Vector{Reference}
end

function pass(x::CSTParser.LeafNode, state::State, s::Scope, index, blockref, delayed)
    state.loc.offset += x.fullspan
end

function pass(x, state::State, s::Scope, index, blockref, delayed)
    ext_binding(x, state, s)
    s1 = create_scope(x, state, s)
    if s1.t == CSTParser.FunctionDef || x isa CSTParser.EXPR{CSTParser.Export}
        delayed = true
    end
    if x isa CSTParser.BinarySyntaxOpCall && x.op.kind == CSTParser.Tokens.DECLARATION
        delayed = false
    end
    get_include(x, state, s1)
    for a in x
        ablockref = get_ref(a, state, s1, blockref, delayed)
        pass(a, state, s1, s1.index, ablockref, delayed)
    end
    s
end

function pass(file::File)
    file.state.loc.offset = 0
    empty!(file.state.bindings)
    empty!(file.state.refs)
    empty!(file.state.includes)
    file.state.bindings["module"] = Binding[]
    file.state.bindings[".used modules"] = Dict{String,Any}(
        "Base" => ModuleBinding(Location(file.state), SIndex(file.index, file.nb), store["Base"]),
         "Core" => ModuleBinding(Location(file.state), SIndex(file.index, file.nb), store["Core"]))
    file.scope = Scope(nothing, Scope[], file.cst.span, CSTParser.TopLevel, file.index, file.nb)
    file.scope = pass(file.cst, file.state, file.scope, file.index, false, false)
end


include("references.jl")
include("utils.jl")
include("symbolserver.jl")
include("documentserver.jl")
include("lint.jl")

const store = StaticLint.SymbolServer.load_store(joinpath(Pkg.API.dir("StaticLint"), "store"))
end

