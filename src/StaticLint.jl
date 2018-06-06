module StaticLint
using CSTParser
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
    t
end
Base.display(b::Binding) = println(b.index, b.pos," @ ",  basename(b.loc.file), ":", b.loc.offset)
Base.display(b::Vector{Binding}) = (println("N = ", length(b));display.(b))

mutable struct Reference{T}
    val::T
    loc::Location
    index::Index
    pos::Int
    delayed::Bool
end

mutable struct ResolvedRef{T}
    r::Reference{T}
    b::Binding
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
    bindings::Dict{String,Vector{Binding}}
    refs::Vector{Reference}
    includes::Vector{Include}
    server
end
State() = State(Location("", 0), Dict{String, Vector{Binding}}(), Reference[], Include[], DocumentServer())

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

function pass(file::File)
    file.state.loc.offset = 0
    empty!(file.state.bindings)
    empty!(file.state.refs)
    empty!(file.state.includes)
    file.state.bindings["using"] = [Binding(Location("", 0), file.index, file.nb, SymbolServer.server["Base"], nothing), Binding(Location("", 0), file.index, file.nb, SymbolServer.server["Core"], nothing)]
    file.state.bindings["module"] = Binding[]
    file.scope = Scope(nothing, Scope[], file.cst.span, CSTParser.TopLevel, file.index, file.nb)
    file.scope = pass(file.cst, file.state, file.scope, file.index, false, false)
end

include("bindings.jl")
include("references.jl")
include("utils.jl")
include("symbolserver.jl")
include("documentserver.jl")
include("lint.jl")

# SymbolServer.init()
# SymbolServer.load_module(Core, true, true)
end

