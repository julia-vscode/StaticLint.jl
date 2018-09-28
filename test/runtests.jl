using StaticLint
using Test

function test_sl(str)
    x = StaticLint.CSTParser.parse(str, true)
    f = StaticLint.File(x)
    StaticLint.pass(f)
    f.state = StaticLint.build_bindings(nothing, f)
    f.rref, f.uref = StaticLint.resolve_refs(f.state.refs, f.state);    
    
    f
end

include("test_bindings.jl")
include("test_imports.jl")