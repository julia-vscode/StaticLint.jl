using StaticLint
using CSTParser, Test
sserver = SymbolServerProcess()
SymbolServer.getstore(sserver)
server = StaticLint.FileServer(Dict(), Set(), sserver.depot);

function get_ids(x, ids = [])
    if x isa CSTParser.IDENTIFIER
        push!(ids, x)
    else
        for a in x
            get_ids(a, ids)
        end
    end
    ids
end

function parse_and_pass(s)
    cst = CSTParser.parse(s, true)
    scope = StaticLint.Scope(nothing, Dict(), Dict{String,Any}("Base" => getsymbolserver(server)["Base"], "Core" => getsymbolserver(server)["Core"]))
    cst.meta.scope = scope.x
    state = StaticLint.State("", scope, nothing, false, false, Dict(), server)
    state(cst)
    return cst
end

function check_resolved(s)
    cst = parse_and_pass(s)
    IDs = get_ids(cst)
    [(i.meta.ref !== nothing) for i in IDs]
end


@testset "Basic bindings" begin 

@test check_resolved("""
x
x = 1
x
""")  == [false, true, true]

@test check_resolved("""
x, y
x = y = 1
x, y
""")  == [false, false, true, true, true, true]

@test check_resolved("""
x, y
x, y = 1, 1
x, y
""")  == [false, false, true, true, true, true]

@test check_resolved("""
M
module M end
M
""")  == [false, true, true]

@test check_resolved("""
f
f() = 0
f
""")  == [false, true, true]

@test check_resolved("""
f
function f end
f
""")  == [false, true, true]

@test check_resolved("""
f
function f() end
f
""")  == [false, true, true]

@test check_resolved("""
function f(a) 
end
""")  == [true, true]

@test check_resolved("""
f, a
function f(a) 
    a
end
f, a
""")  == [false, false, true, true, true, true, false]


@test check_resolved("""
x
let x = 1
    x
end
x
""")  == [false, true, true, false]

@test check_resolved("""
x,y
let x = 1, y = 1
    x, y
end
x, y
""")  == [false, false, true, true, true, true, false, false]

@test check_resolved("""
function f(a...)
    f(a)
end
""")  == [true, true, true, true]

@test check_resolved("""
for i = 1:1
end
""")  == [true]

@test check_resolved("""
[i for i in 1:1]
""")  == [true, true]

@test check_resolved("""
[i for i in 1:1 if i]
""")  == [true, true, true]

@test check_resolved("""
@deprecate f(a) sin(a)
f
""")  == [true, true, true, true, true, true]

@test check_resolved("""
@deprecate f sin
f
""")  == [true, true, true, true]

@test check_resolved("""
@enum(E,a,b)
E
a
b
""")  == [true, true, true, true, true, true, true]

@test check_resolved("""
module Mod
f = 1
end
using .Mod: f
f
""") == [true, true, true, true, true]

@test check_resolved("""
module Mod
module SubMod
    f() = 1
end
using .SubMod: f
f
end
""") == [true, true, true, true, true, true]

end