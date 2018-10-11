module StaticLint
using CSTParser, Pkg
const Index = Tuple
struct SIndex{N}
    i::NTuple{N,Int}
    n::Int
end

mutable struct Location
    file::String
    offset::Int
end

mutable struct Reference{T}
    val::T
    loc::Location
    si::SIndex
    delayed::Bool
end

include("bindings.jl")

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
    bindings
    modules::Vector{Binding}
    exports::Dict{Tuple,Vector{String}}
    imports::Vector{ImportBinding}
    used_modules::Dict{String,Binding}
    refs::Vector{Reference}
    includes::Vector{Include}
    server
end
State() = State(Location("", 0), Dict{Tuple,Any}(), Binding[], Dict{Tuple,Vector}(),ImportBinding[], Dict{String,Binding}(), Reference[], Include[], DocumentServer())
State(path::String, server) = State(Location(path, 0), Dict{Tuple,Any}(), Binding[], Dict{Tuple,Vector}(),ImportBinding[], Dict{String,Binding}(), Reference[], Include[], server)
function Base.display(state::State)
    println("[State ($(state.loc.file)) w/ ")
    println("      $(length(state.bindings)) bindings") 
    println("      $(length(state.modules)) modules")     
    println("      $(length(state.refs)) references]")   
end


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
File(x::CSTParser.EXPR) = File(x, State(), Scope(), (), 0, "", [], [])

function pass(x::CSTParser.LeafNode, state::State, s::Scope, index, blockref, delayed)
    state.loc.offset += x.fullspan
end

function pass(x, state::State, s::Scope, index, blockref, delayed)
    # Get external bindings generated by `x`.
    ext_binding(x, state, s)
    # Create new scope (if needed) for traversing through `x`.
    s1 = create_scope(x, state, s)
    # Internal scope evaluation is delayed
    delayed = s1.t == CSTParser.FunctionDef || x isa CSTParser.EXPR{CSTParser.Export}
    # Overrides the above, type declarations must refer to previously defined types
    delayed = !(x isa CSTParser.BinarySyntaxOpCall && x.op.kind == CSTParser.Tokens.DECLARATION)
    # Check whether `x` includes a file.
    get_include(x, state, s1)
    # Traverse sub expressions of `x`.
    for a in x
        ablockref = get_ref(a, state, s1, blockref, delayed)
        pass(a, state, s1, s1.index, ablockref, delayed)
    end
    s
end

function pass(x::CSTParser.EXPR{CSTParser.Kw}, state::State, s::Scope, index, blockref, delayed)
    if x.args[1] isa CSTParser.IDENTIFIER
        state.loc.offset += x.args[1].fullspan + x.args[2].fullspan
        pass(x.args[3], state, s, s.index, blockref, delayed)
    else
        for a in x
            ablockref = get_ref(a, state, s, blockref, delayed)
            pass(a, state, s, s.index, ablockref, delayed)
        end
        s
    end        
end

function pass(x::CSTParser.EXPR{CSTParser.Try}, state::State, s::Scope, index, blockref, delayed)
    s1 = create_scope(x, state, s)
    it = 1
    for a in x
        if it == 4 && a isa CSTParser.IDENTIFIER
            add_binding(CSTParser.str_value(a), a, state, s1)
        end
        ablockref = get_ref(a, state, s1, blockref, delayed)
        pass(a, state, s1, s1.index, ablockref, delayed)
        it += 1
    end
end


function pass(file::File)
    file.state.loc.offset = 0
    empty!(file.state.refs)
    empty!(file.state.includes)
    empty!(file.state.bindings)
    empty!(file.state.modules)
    empty!(file.state.imports)
    empty!(file.state.exports)
    empty!(file.state.used_modules)
    file.scope = Scope(nothing, Scope[], file.cst.span, CSTParser.TopLevel, file.index, file.nb)
    file.scope = pass(file.cst, file.state, file.scope, file.index, false, false)
end


include("references.jl")
include("utils.jl")
include("documentserver.jl")
include("helpers.jl")

# const store = SymbolServer.build_base_store()
# const _Module = store["Core"]["Module"]
# const _DataType = store["Core"]["DataType"]
# const _Function = store["Core"]["Function"]

global store = nothing
global _Module = nothing
global _DataType = nothing
global _Function = nothing

function setstore(new_store)
    global store = new_store
    global _Module = store["Core"]["Module"]
    global _DataType = store["Core"]["DataType"]
    global _Function = store["Core"]["Function"]
end

end
