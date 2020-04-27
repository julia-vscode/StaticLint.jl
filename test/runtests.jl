using StaticLint, SymbolServer
using CSTParser, Test
using StaticLint: scopeof, bindingof, refof, errorof, check_all

server = StaticLint.FileServer();

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
    empty!(server.files)
    f = StaticLint.File("", s, CSTParser.parse(s, true), nothing, server)
    StaticLint.setroot(f, f)
    StaticLint.setfile(server, "", f)
    StaticLint.scopepass(f)
    return f.cst
end


function check_resolved(s)
    cst = parse_and_pass(s)
    IDs = get_ids(cst)
    [(refof(i) !== nothing) for i in IDs]
end

@testset "StaticLint" begin

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

@test check_resolved("-(r::T) where T = r") == [1, 1, 1, 1]
@test check_resolved("[k * j for j = 1:10 for k = 1:10]") == [1, 1, 1, 1]
@test check_resolved("[k * j for j in 1:10 for k in 1:10]") == [1, 1, 1, 1]

@testset "inference" begin
    @test bindingof(parse_and_pass("f(arg) = arg")[1]).type == StaticLint.CoreTypes.Function
    @test bindingof(parse_and_pass("function f end")[1]).type == StaticLint.CoreTypes.Function
    @test bindingof(parse_and_pass("struct T end")[1]).type == StaticLint.CoreTypes.DataType
    @test bindingof(parse_and_pass("mutable struct T end")[1]).type == StaticLint.CoreTypes.DataType
    @test bindingof(parse_and_pass("abstract type T end")[1]).type == StaticLint.CoreTypes.DataType
    @test bindingof(parse_and_pass("primitive type T 8 end")[1]).type == StaticLint.CoreTypes.DataType
    @test bindingof(parse_and_pass("x = 1")[1][1]).type == StaticLint.CoreTypes.Int
    @test bindingof(parse_and_pass("x = 1.0")[1][1]).type == StaticLint.CoreTypes.Float64
    @test bindingof(parse_and_pass("x = \"text\"")[1][1]).type == StaticLint.CoreTypes.String
    @test bindingof(parse_and_pass("module A end")[1]).type == StaticLint.CoreTypes.Module
    @test bindingof(parse_and_pass("baremodule A end")[1]).type == StaticLint.CoreTypes.Module

    # @test parse_and_pass("function f(x::Int) x end")[1][2][3].binding.t == StaticLint.getsymbolserver(server)["Core"].vals["Function"]
    let cst = parse_and_pass("""
        struct T end
        function f(x::T) x end""")
        @test bindingof(cst[1]).type == StaticLint.CoreTypes.DataType
        @test bindingof(cst[2]).type == StaticLint.CoreTypes.Function
        @test bindingof(cst[2][2][3]).type == bindingof(cst[1])
        @test refof(cst[2][3][1]) == bindingof(cst[2][2][3])
    end
    let cst = parse_and_pass("""
        struct T end
        T() = 1
        function f(x::T) x end""")
        @test bindingof(cst[1]).type == StaticLint.CoreTypes.DataType
        @test bindingof(cst[3]).type == StaticLint.CoreTypes.Function
        @test bindingof(cst[3][2][3]).type == bindingof(cst[1])
        @test refof(cst[3][3][1]) == bindingof(cst[3][2][3])
    end
    
    let cst = parse_and_pass("""
        struct T end
        t = T()""")
        @test bindingof(cst[1]).type == StaticLint.CoreTypes.DataType
        @test bindingof(cst[2][1]).type == bindingof(cst[1])
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
        check_all(cst, StaticLint.LintOptions(),server)
        @test errorof(cst[1]) === StaticLint.IncorrectCallArgs
    end
    let cst = parse_and_pass("""
        for i in length(1) end
        for i in 1.1 end
        for i in 1 end
        for i in 1:1 end
        """)
        check_all(cst, StaticLint.LintOptions(),server)
        @test errorof(cst[1][2]) === StaticLint.IncorrectIterSpec
        @test errorof(cst[2][2]) === StaticLint.IncorrectIterSpec
        @test errorof(cst[3][2]) === StaticLint.IncorrectIterSpec
        @test errorof(cst[4][2]) === nothing
    end

    let cst = parse_and_pass("""
        [i for i in length(1) end]
        [i for i in 1.1 end]
        [i for i in 1 end]
        [i for i in 1:1 end]
        """)
        check_all(cst, StaticLint.LintOptions(),server)
        @test errorof(cst[1][2][3]) === StaticLint.IncorrectIterSpec
        @test errorof(cst[2][2][3]) === StaticLint.IncorrectIterSpec
        @test errorof(cst[3][2][3]) === StaticLint.IncorrectIterSpec
        @test errorof(cst[4][2][3]) === nothing
    end

    let cst = parse_and_pass("a == nothing")
        check_all(cst, StaticLint.LintOptions(),server)
        @test errorof(cst[1][2]) === StaticLint.NothingEquality 
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
        @test refof(cst[1]) === nothing
        @test refof(cst[2]) === nothing
        @test refof(cst[3][3][1]) !== nothing
        @test refof(cst[3][3][2]) !== nothing
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

@testset "tuple args" begin
    let cst = parse_and_pass("""
        function f((arg1, arg2))
            arg1, arg2
        end""")
        @test StaticLint.hasref(cst[1][3][1][1])
        @test StaticLint.hasref(cst[1][3][1][3])
    end

    let cst = parse_and_pass("""
        function f((arg1, arg2) = (1,2))
            arg1, arg2
        end""")
        @test StaticLint.hasref(cst[1][3][1][1])
        @test StaticLint.hasref(cst[1][3][1][3])
    end

    let cst = parse_and_pass("""
        function f((arg1, arg2)::Tuple{Int,Int})
            arg1, arg2
        end""")
        @test StaticLint.hasref(cst[1][3][1][1])
        @test StaticLint.hasref(cst[1][3][1][3])
    end
end

@testset "type params check" begin
    let cst = parse_and_pass("""
        f() where T
        f() where {T,S}
        f() where {T<:Any}
        """)
        StaticLint.check_all(cst, StaticLint.LintOptions(), server)
        @test StaticLint.errorof(cst[1][3]) == StaticLint.UnusedTypeParameter
        @test StaticLint.errorof(cst[2][4]) == StaticLint.UnusedTypeParameter
        @test StaticLint.errorof(cst[2][6]) == StaticLint.UnusedTypeParameter
        @test StaticLint.errorof(cst[3][4]) == StaticLint.UnusedTypeParameter
    end
    let cst = parse_and_pass("""
        f(x::T) where T
        f(x::T,y::S) where {T,S}
        f(x::T) where {T<:Any}
        """)
        StaticLint.check_all(cst, StaticLint.LintOptions(), server)
        @test !StaticLint.haserror(cst[1][3])
        @test !StaticLint.haserror(cst[2][4])
        @test !StaticLint.haserror(cst[2][6])
        @test !StaticLint.haserror(cst[3][4])
    end
end


@testset "overwrites_imported_function" begin
    let cst = parse_and_pass("""
        import Base:sin
        using Base:cos
        sin(x) = 1
        cos(x) = 1
        Base.tan(x) = 1
        """)
        
        @test StaticLint.overwrites_imported_function(bindingof(cst[3]))
        @test !StaticLint.overwrites_imported_function(bindingof(cst[4]))
        @test StaticLint.overwrites_imported_function(bindingof(cst[5]))
    end
end

@testset "pirates" begin
    let cst = parse_and_pass("""
        import Base:sin
        struct T end
        sin(x::Int) = 1
        sin(x::T) = 1
        sin(x::Array{T}) = 1
        """)
        StaticLint.check_for_pirates(cst[3])
        StaticLint.check_for_pirates(cst[4])
        @test errorof(cst[3]) === StaticLint.TypePiracy
        @test errorof(cst[4]) === nothing
    end
    let cst = parse_and_pass("""
        struct AreaIterator{T}
            array::AbstractMatrix{T}
            radius::Int
        end
        Base.eltype(::Type{AreaIterator{T}}) where T = Tuple{T, AbstractVector{T}}
        """)
        StaticLint.check_for_pirates(cst[2])
        @test errorof(cst[2]) === nothing
    end
end

@testset "docs for undescribed variables" begin
let cst = parse_and_pass("""
    \"\"\"
        somefunc() = true
    \"\"\"
    somefunc
    somefunc() = true
    """)
    @test StaticLint.hasref(cst[1][3])
    @test StaticLint.hasbinding(cst[1][3])
    @test refof(cst[1][3]) == bindingof(cst[1][3])
end
end

@testset "check_call" begin
    let cst = parse_and_pass("""
        sin(1)
        sin(1,2)
        """)
        StaticLint.check_call(cst[1], server)
        StaticLint.check_call(cst[2], server)
        @test StaticLint.errorof(cst[1]) === nothing
        @test StaticLint.errorof(cst[2]) == StaticLint.IncorrectCallArgs
    end

    let cst = parse_and_pass("""
        Base.sin(a,b) = 1
        function Base.sin(a,b)
            1
        end
        """)
        StaticLint.check_call(cst[1][1], server)
        @test StaticLint.errorof(cst[1][1]) === nothing
        StaticLint.check_call(cst[2][2], server)
        @test StaticLint.errorof(cst[2][2]) === nothing
    end

    let cst = parse_and_pass("""
        f(x) = 1
        f(1, 2)
        """)
        StaticLint.check_call(cst[2], server)
        @test StaticLint.errorof(cst[2]) === StaticLint.IncorrectCallArgs
    end

    let cst = parse_and_pass("""
        view([1], 1, 2, 3)
        """)
        StaticLint.check_call(cst[1], server)
        @test StaticLint.errorof(cst[1]) === nothing
    end

    let cst = parse_and_pass("""
        f(a...) = 1
        f(1)
        f(1, 2)
        """)
        StaticLint.check_call(cst[2], server)
        StaticLint.check_call(cst[3], server)
        @test StaticLint.errorof(cst[2]) === nothing
        @test StaticLint.errorof(cst[3]) === nothing
    end
    let cst = parse_and_pass("""
        function func(a, b)
            func(a...)
        end
        """)
        StaticLint.check_call(cst[1][3][1], server)
        m_counts = StaticLint.func_nargs(cst[1])
        call_counts = StaticLint.call_nargs(cst[1][3][1])
        @test StaticLint.errorof(cst[1][3][1]) === nothing
    end
    let cst = parse_and_pass("""
        function func(@nospecialize args...) end
        func(1, 2)
        """)
        @test StaticLint.func_nargs(cst[1]) == (0, typemax(Int), String[], false)
        StaticLint.check_call(cst[2], server)
        @test StaticLint.errorof(cst[2]) === nothing
    end
    let cst = parse_and_pass("""
        argtail(x, rest...) = 1
        tail(x::Tuple) = argtail(x...)
        """)
        @test StaticLint.func_nargs(cst[1]) == (1, typemax(Int), String[], false)
        StaticLint.check_call(cst[2], server)
        @test StaticLint.errorof(cst[2]) === nothing
    end
    let cst = parse_and_pass("""
        func(arg::Vararg{T,N}) where N = arg
        func(a,b)
        """)

        @test StaticLint.func_nargs(cst[1]) == (0, typemax(Int), String[], false)
        StaticLint.check_call(cst[2], server)
        @test StaticLint.errorof(cst[2]) === nothing
    end
    let cst = parse_and_pass("""
        function f(a, b; kw = kw) end
        f(1,2, kw = 1)
        """)
        StaticLint.check_call(cst[2], server)
        @test StaticLint.errorof(cst[2]) === nothing
    end
    let cst = parse_and_pass("""
        func(a,b,c,d) = 1
        func(a..., 2)
        """)
        StaticLint.call_nargs(cst[2])
        StaticLint.check_call(cst[2], server)
        @test StaticLint.errorof(cst[2]) === nothing
    end
    let cst = parse_and_pass("""
        @kwdef struct A
            x::Float64
        end
        A(x = 5.0)
        """)
        StaticLint.check_call(cst[2], server)
        @test StaticLint.errorof(cst[2]) === nothing
    end
end

@testset "check_modulename" begin
    let cst = parse_and_pass("""
        module Mod1
        module Mod11
        end
        end
        module Mod2
        module Mod2
        end
        end
        """)
        StaticLint.check_modulename(cst[1])
        StaticLint.check_modulename(cst[1][3][1])
        StaticLint.check_modulename(cst[2])
        StaticLint.check_modulename(cst[2][3][1])
        
        @test StaticLint.errorof(cst[1][2]) === nothing
        @test StaticLint.errorof(cst[1][3][1][2]) === nothing
        @test StaticLint.errorof(cst[2][2]) === nothing
        @test StaticLint.errorof(cst[2][3][1][2]) === StaticLint.InvalidModuleName
    end
end

if !(VERSION < v"1.3")
@testset "non-std var syntax" begin
    let cst = parse_and_pass("""
        var"name" = 1
        var"func"(arg) = arg
        function var"func1"() end
        name
        func
        func1
        """)
        StaticLint.collect_hints(cst)
        @test all(n in keys(cst.meta.scope.names) for n in ("name", "func"))
        @test StaticLint.hasref(cst[4])
        @test StaticLint.hasref(cst[5])
        @test StaticLint.hasref(cst[6])
    end
end
end

if false # Not to be run, requires JuMP
    @testset "JuMP macros" begin
let cst = parse_and_pass("""
    using JuMP
    model = Model()
    some_bound = 1
    @variable(model, x0)
    @variable(model, x1, somekw=1)
    @variable(model, x2 <= 1)
    @variable(model, x3 >= 1)
    @variable(model, 1 <= x4)
    @variable(model, 1 >= x5)
    @variable(model, x6 >= some_bound)
    # @variable(model, some_bound >= x7)
    """)
    @test isempty(StaticLint.collect_hints(cst))
end

let cst = parse_and_pass("""
    using JuMP
    model = Model()
    some_bound = 1
    @variable model x0
    @variable model x1 somekw=1
    @variable model x2 <= 1
    @variable model x3 >= 1
    @variable model 1 <= x4
    @variable model 1 >= x5
    @variable model x6 >= some_bound
    # @variable(model, some_bound >= x7)
    """)
    @test isempty(StaticLint.collect_hints(cst))
end

let cst = parse_and_pass("""
    using JuMP
    model = Model()
    some_bound = 1
    @variable(model, some_bound >= x7)
    """)
    @test !StaticLint.hasref(cst[4][5][3])
end

let cst = parse_and_pass("""
    using JuMP
    model = Model()
    some_bound = 1
    @expression(model, ex, some_bound >= 1)
    """)
    @test isempty(StaticLint.collect_hints(cst))
end

let cst = parse_and_pass("""
    using JuMP
    model = Model()
    @expression(model, expr, 1 == 1)
    @constraint(model, con1, expr)
    @constraint model con2 expr
    """)
    @test isempty(StaticLint.collect_hints(cst))
end
end
end

@testset "stdcall" begin
    let cst = parse_and_pass("""
        ccall(:GetCurrentProcess, stdcall, Ptr{Cvoid}, ())""")
        StaticLint.collect_hints(cst)
        @test isempty(StaticLint.collect_hints(cst))
    end
    let cst = parse_and_pass("""
        stdcall
        """)
        @test !StaticLint.hasref(cst[1])
    end
end

@testset "check_if_conds" begin
    let cst = parse_and_pass("""
        if true end
        """)
        StaticLint.check_if_conds(cst[1])
        @test cst[1][2].meta.error == StaticLint.ConstIfCondition
    end
    let cst = parse_and_pass("""
        if x = 1 end
        """)
        StaticLint.check_if_conds(cst[1])
        @test cst[1][2].meta.error == StaticLint.EqInIfConditional
    end
    let cst = parse_and_pass("""
        if a || x = 1 end
        """)
        StaticLint.check_if_conds(cst[1])
        @test cst[1][2].meta.error == StaticLint.EqInIfConditional
    end
    let cst = parse_and_pass("""
        if x = 1 && b end
        """)
        StaticLint.check_if_conds(cst[1])
        @test cst[1][2].meta.error == StaticLint.EqInIfConditional
    end
end

@testset "check redefinition of const" begin
    let cst = parse_and_pass("""
        T = 1
        struct T end
        """)
        StaticLint.check_const_decl(cst[2])
        @test cst[2].meta.error == StaticLint.CannotDeclareConst
    end
    let cst = parse_and_pass("""
        struct T end
        T = 1
        """)
        StaticLint.check_const_redef(cst[2][1])
        @test cst[2][1].meta.error == StaticLint.InvalidRedefofConst
    end
    let cst = parse_and_pass("""
        struct T end
        T() = 1
        """)
        StaticLint.check_const_redef(cst[2])
        @test cst[2].meta.error == nothing
    end
end

end
