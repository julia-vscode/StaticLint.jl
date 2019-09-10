using StaticLint, SymbolServer
using CSTParser, Test
using StaticLint: scopeof, bindingof, refof

sserver = SymbolServerProcess()
SymbolServer.getstore(sserver)
@info join(collect(keys(sserver.depot)), ", ")
server = StaticLint.FileServer(Dict(), Set(), sserver.depot);

function get_ids(x, ids = [])
    if StaticLint.typof(x) == CSTParser.IDENTIFIER
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
    scope = StaticLint.Scope(nothing, Dict(), Dict{String,Any}("Base" => StaticLint.getsymbolserver(server)["Base"], "Core" => StaticLint.getsymbolserver(server)["Core"]), false)
    StaticLint.setscope!(cst, scope)
    state = StaticLint.State("", scope, false, false, false, [], server)
    state(cst)
    return cst
end

function check_resolved(s)
    cst = parse_and_pass(s)
    IDs = get_ids(cst)
    [(i.ref !== nothing) for i in IDs]
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

# @test check_resolved("""
# @deprecate f(a) sin(a)
# f
# """)  == [true, true, true, true, true, true]

@test check_resolved("""
@deprecate f sin
f
""")  == [true, true, true, true]

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

@test check_resolved("""
struct T
    field
end
function f(arg::T)
    arg.field
end
""") == [true, true, true, true, true, true, true]

@test check_resolved("""
f(arg) = arg
""") == [1, 1, 1]

@testset "inference" begin
    @test bindingof(parse_and_pass("f(arg) = arg")[1]).t == StaticLint.getsymbolserver(server)["Core"].vals["Function"]
    @test bindingof(parse_and_pass("function f end")[1]).t == StaticLint.getsymbolserver(server)["Core"].vals["Function"]
    @test bindingof(parse_and_pass("struct T end")[1]).t == StaticLint.getsymbolserver(server)["Core"].vals["DataType"]
    @test bindingof(parse_and_pass("mutable struct T end")[1]).t == StaticLint.getsymbolserver(server)["Core"].vals["DataType"]
    @test bindingof(parse_and_pass("abstract type T end")[1]).t == StaticLint.getsymbolserver(server)["Core"].vals["DataType"]
    @test bindingof(parse_and_pass("primitive type T 8 end")[1]).t == StaticLint.getsymbolserver(server)["Core"].vals["DataType"]
    @test bindingof(parse_and_pass("x = 1")[1][1]).t == StaticLint.getsymbolserver(server)["Core"].vals["Int"]
    @test bindingof(parse_and_pass("x = 1.0")[1][1]).t == StaticLint.getsymbolserver(server)["Core"].vals["Float64"]
    @test bindingof(parse_and_pass("x = \"text\"")[1][1]).t == StaticLint.getsymbolserver(server)["Core"].vals["String"]
    @test bindingof(parse_and_pass("module A end")[1]).t == StaticLint.getsymbolserver(server)["Core"].vals["Module"]
    @test bindingof(parse_and_pass("baremodule A end")[1]).t == StaticLint.getsymbolserver(server)["Core"].vals["Module"]

    # @test parse_and_pass("function f(x::Int) x end")[1][2][3].binding.t == StaticLint.getsymbolserver(server)["Core"].vals["Function"]
    let cst = parse_and_pass("""
        struct T end
        function f(x::T) x end""")
        @test bindingof(cst[1]).t == StaticLint.getsymbolserver(server)["Core"].vals["DataType"]
        @test bindingof(cst[2]).t == StaticLint.getsymbolserver(server)["Core"].vals["Function"]
        @test bindingof(cst[2][2][3]).t == bindingof(cst[1])
        @test refof(cst[2][3][1]) == bindingof(cst[2][2][3])
    end
    let cst = parse_and_pass("""
        struct T end
        T() = 1
        function f(x::T) x end""")
        @test bindingof(cst[1]).t == StaticLint.getsymbolserver(server)["Core"].vals["DataType"]
        @test bindingof(cst[3]).t == StaticLint.getsymbolserver(server)["Core"].vals["Function"]
        @test bindingof(cst[3][2][3]).t == bindingof(cst[1])
        @test refof(cst[3][3][1]) == bindingof(cst[3][2][3])
    end
    
    let cst = parse_and_pass("""
        struct T end
        t = T()""")
        @test bindingof(cst[1]).t == StaticLint.getsymbolserver(server)["Core"].vals["DataType"]
        @test bindingof(cst[2][1]).t == bindingof(cst[1])
    end

    let cst = parse_and_pass("""
        module A
        module B
        x = 1
        end
        module C
        import ..B
        B.x
        end
        end""")
        @test refof(cst[1][3][2][3][2][3][1]) == bindingof(cst[1][3][1][3][1][1])
    end

    let cst = parse_and_pass("""
        struct T0
            x
        end
        struct T1
            field::T0
        end
        function f(arg::T1)
            arg.field.x
        end""");
        @test refof(cst[3][3][1][1][1]) == bindingof(cst[3][2][3])
        @test refof(cst[3][3][1][1][3][1]) == bindingof(cst[2][3][1])
        @test refof(cst[3][3][1][3][1]) == bindingof(cst[1][3][1])
    end
   
    
    let cst = parse_and_pass("""
        raw"whatever"
        """)
        @test refof(cst[1][1]) !== nothing
    end
    let cst = parse_and_pass("""
        macro mac_str() end
        mac"whatever"
        """)
        @test refof(cst[2][1]) == bindingof(cst[1])
    end
    
    let cst = parse_and_pass("""
        [i * j for i = 1:10 for j = i:10]
        """)
        @test refof(cst[1][2][1][3][3][1]) == bindingof(cst[1][2][1][1][3][1])
    end
    let cst = parse_and_pass("""
        [i * j for i = 1:10, j = 1:10 for k = i:10]
        """)
        @test refof(cst[1][2][1][3][3][1]) == bindingof(cst[1][2][1][1][3][1])
    end
    
    let cst = parse_and_pass("""
        module Reparse
        end
        using .Reparse, CSTParser
        """)
        @test refof(cst[2][3]).val == bindingof(cst[1])
    end

    let cst = parse_and_pass("""
        module A
        A
        end
        """)
        @test scopeof(cst).names["A"] == scopeof(cst[1]).names["A"]
        @test refof(cst[1][2]) == bindingof(cst[1])
        @test refof(cst[1][3][1]) == bindingof(cst[1])
    end
    # let cst = parse_and_pass("""
    #     using Test: @test
    #     """)
    #     @test bindingof(cst[1][4]) !== nothing
    # end
    let cst = parse_and_pass("""
        sin(1,2,3)
        """)
        @test_broken refof(cst[1]) === StaticLint.IncorrectCallNargs
    end
    let cst = parse_and_pass("""
        for i in length(1) end
        for i in 1.1 end
        for i in 1 end
        for i in 1:1 end
        """)
        @test refof(cst[1][2]) === StaticLint.IncorrectIterSpec
        @test refof(cst[2][2]) === StaticLint.IncorrectIterSpec
        @test refof(cst[3][2]) === StaticLint.IncorrectIterSpec
        @test refof(cst[4][2]) === nothing
    end

    let cst = parse_and_pass("""
        [i for i in length(1) end]
        [i for i in 1.1 end]
        [i for i in 1 end]
        [i for i in 1:1 end]
        """)
        @test refof(cst[1][2][3]) === StaticLint.IncorrectIterSpec
        @test refof(cst[2][2][3]) === StaticLint.IncorrectIterSpec
        @test refof(cst[3][2][3]) === StaticLint.IncorrectIterSpec
        @test refof(cst[4][2][3]) === nothing
    end

    let cst = parse_and_pass("a == nothing")
        @test refof(cst[1][2]) === StaticLint.NothingEquality 
    end

    let cst = parse_and_pass("""
        struct Graph
            children:: T
        end
        
        function test()
            g = Graph()
            f = g.children
        end""")
        @test cst[2][3][2][3][3][1] in bindingof(cst[1][3][1]).refs
    end

    let cst = parse_and_pass("""
        __source__
        __module__
        macro m()
            __source__
            __module__
        end""")
        @test cst[1].ref === nothing
        @test cst[2].ref === nothing
        @test cst[3][3][1].ref == StaticLint.NoReference
        @test cst[3][3][2].ref == StaticLint.NoReference
    end
end

@testset "macros" begin
    @test check_resolved("""
    @enum(E,a,b)
    E
    a
    b
    """)  == [true, true, true, true, true, true, true]
    end

    @test check_resolved("""
    @enum E a b 
    E
    a
    b
    """)  == [true, true, true, true, true, true, true]

    @test check_resolved("""
    @enum E begin
        a
        b
    end
    E
    a
    b
    """)  == [true, true, true, true, true, true, true]
end