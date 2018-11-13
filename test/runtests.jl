using StaticLint,SymbolServer
using Test

const pkgs = (depot = SymbolServer.load_core();SymbolServer.import_package("StaticLint"=>"StaticLint", depot);depot["packages"])
function test_sl(str)
    x = StaticLint.CSTParser.parse(str, true)
    f = StaticLint.File(x, pkgs)
    StaticLint.pass(f)
    state = StaticLint.build_bindings(f)
    StaticLint.resolve_refs(f.state.refs, state, f.rref, f.uref);    
    f.state.bindings = state.bindings
    return f
end

include("test_bindings.jl")
include("test_imports.jl")