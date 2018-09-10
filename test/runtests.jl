using StaticLint
using Test

str = """
var1 = 1
var1
"""
x = StaticLint.CSTParser.parse(str, true)
f = StaticLint.File(x)
StaticLint.pass(f)
rref, uref = StaticLint.resolve_refs(f.state.refs, f.state)
@test rref[1].b == f.state.bindings["var1"][1]
