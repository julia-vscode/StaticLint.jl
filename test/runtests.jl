using TestItemRunner

@run_package_tests

@testmodule SLSetup begin
    using StaticLint, SymbolServer
    using CSTParser, Test
    using StaticLint: scopeof, bindingof, refof, errorof, check_all, getenv

    export StaticLint, SymbolServer, CSTParser
    export scopeof, bindingof, refof, errorof, check_all, getenv
    export server, get_ids, parse_and_pass, check_resolved
    export module_name, find_module_by_name, find_first

    server = StaticLint.FileServer()

    function get_ids(x, ids = [])
        if StaticLint.headof(x) === :IDENTIFIER
            push!(ids, x)
        elseif x.args !== nothing
            for a in x.args
                get_ids(a, ids)
            end
        end
        ids
    end

    parse_and_pass(s) = StaticLint.lint_string(s, server)

    function check_resolved(s)
        cst = parse_and_pass(s)
        IDs = get_ids(cst)
        [(refof(i) !== nothing) for i in IDs]
    end

    # Simple iterative DFS utilities (no recursive predicate calls)
    function module_name(ex::CSTParser.EXPR)::Union{String, Nothing}
        if CSTParser.defines_module(ex)
            n = CSTParser.get_name(ex)
            if CSTParser.isidentifier(n)
                return CSTParser.valof(n)
            elseif StaticLint.headof(n) === :NONSTDIDENTIFIER && length(n.args) == 2
                return CSTParser.valof(n.args[2])
            end
        end
        return nothing
    end

    function find_module_by_name(root::CSTParser.EXPR, name::String)
        stack = CSTParser.EXPR[root]
        while !isempty(stack)
            x = pop!(stack)
            if module_name(x) == name
                return x
            end
            if x.args !== nothing
                # push children
                for a in x.args
                    a isa CSTParser.EXPR && push!(stack, a)
                end
            end
        end
        return nothing
    end

    function find_first(root::CSTParser.EXPR, f::Function)
        stack = CSTParser.EXPR[root]
        while !isempty(stack)
            x = pop!(stack)
            if f(x)
                return x
            end
            if x.args !== nothing
                for a in x.args
                    a isa CSTParser.EXPR && push!(stack, a)
                end
            end
        end
        return nothing
    end
    # Adapter to support weird block call
    find_first(f::Function, root::CSTParser.EXPR) = find_first(root, f)
end

@testitem "Basic bindings" setup = [SLSetup] begin

    @test check_resolved(
        """
        x
        x = 1
        x
        """
    ) == [false, true, true]

    @test check_resolved(
        """
        x, y
        x = y = 1
        x, y
        """
    ) == [false, false, true, true, true, true]

    @test check_resolved(
        """
        x, y
        x, y = 1, 1
        x, y
        """
    ) == [false, false, true, true, true, true]

    @test check_resolved(
        """
        M
        module M end
        M
        """
    ) == [false, true, true]

    @test check_resolved(
        """
        f
        f() = 0
        f
        """
    ) == [false, true, true]

    @test check_resolved(
        """
        f
        function f end
        f
        """
    ) == [false, true, true]

    @test check_resolved(
        """
        f
        function f() end
        f
        """
    ) == [false, true, true]

    @test check_resolved(
        """
        function f(a)
        end
        """
    ) == [true, true]

    @test check_resolved(
        """
        f, a
        function f(a)
            a
        end
        f, a
        """
    ) == [false, false, true, true, true, true, false]


    @test check_resolved(
        """
        x
        let x = 1
            x
        end
        x
        """
    ) == [false, true, true, false]

    @test check_resolved(
        """
        x,y
        let x = 1, y = 1
            x, y
        end
        x, y
        """
    ) == [false, false, true, true, true, true, false, false]

    @test check_resolved(
        """
        function f(a...)
            f(a)
        end
        """
    ) == [true, true, true, true]

    @test check_resolved(
        """
        for i = 1:1
        end
        """
    ) == [true]

    @test check_resolved(
        """
        [i for i in 1:1]
        """
    ) == [true, true]

    @test check_resolved(
        """
        [i for i in 1:1 if i]
        """
    ) == [true, true, true]

    # @test check_resolved("""
    # @deprecate f(a) sin(a)
    # f
    # """)  == [true, true, true, true, true, true]

    @test check_resolved(
        """
        @deprecate f sin
        f
        """
    ) == [true, true, true, true]

    @test check_resolved(
        """
        module Mod
        f = 1
        end
        using .Mod: f
        f
        """
    ) == [true, true, true, true, true]

    @test check_resolved(
        """
        module Mod
        module SubMod
            f() = 1
        end
        using .SubMod: f
        f
        end
        """
    ) == [true, true, true, true, true, true]

    @test check_resolved(
        """
        struct T
            field
        end
        function f(arg::T)
            arg.field
        end
        """
    ) == [true, true, true, true, true, true, true]

    if VERSION > v"1.8-"
        @test check_resolved(
            """
            mutable struct T
                const field
            end
            function f(arg::T)
                arg.field
            end
            """
        ) == [true, true, true, true, true, true, true]
    end

    @test check_resolved(
        """
        f(arg) = arg
        """
    ) == [1, 1, 1]

    @test check_resolved("-(r::T) where T = r") == [1, 1, 1, 1]
    @test check_resolved("[k * j for j = 1:10 for k = 1:10]") == [1, 1, 1, 1]
    @test check_resolved("[k * j for j in 1:10 for k in 1:10]") == [1, 1, 1, 1]

    @testset "inference" begin
        @test StaticLint.CoreTypes.isfunction(bindingof(parse_and_pass("f(arg) = arg").args[1]).type)
        @test StaticLint.CoreTypes.isfunction(bindingof(parse_and_pass("function f end").args[1]).type)
        @test StaticLint.CoreTypes.isdatatype(bindingof(parse_and_pass("struct T end").args[1]).type)
        @test StaticLint.CoreTypes.isdatatype(bindingof(parse_and_pass("mutable struct T end").args[1]).type)
        @test StaticLint.CoreTypes.isdatatype(bindingof(parse_and_pass("abstract type T end").args[1]).type)
        @test StaticLint.CoreTypes.isdatatype(bindingof(parse_and_pass("primitive type T 8 end").args[1]).type)
        @test StaticLint.CoreTypes.isint(bindingof(parse_and_pass("x = 1").args[1].args[1]).type)
        @test StaticLint.CoreTypes.isfloat(bindingof(parse_and_pass("x = 1.0").args[1].args[1]).type)
        @test StaticLint.CoreTypes.isstring(bindingof(parse_and_pass("x = \"text\"").args[1].args[1]).type)
        @test StaticLint.CoreTypes.ismodule(bindingof(parse_and_pass("module A end").args[1]).type)
        @test StaticLint.CoreTypes.ismodule(bindingof(parse_and_pass("baremodule A end").args[1]).type)

        # @test parse_and_pass("function f(x::Int) x end")[1][2][3].binding.t == StaticLint.getsymbolserver(server)["Core"].vals["Function"]
        let cst = parse_and_pass(
                """
                struct T end
                            function f(x::T) x end
                            """
            )
            @test StaticLint.CoreTypes.isdatatype(bindingof(cst.args[1]).type)
            @test StaticLint.CoreTypes.isfunction(bindingof(cst.args[2]).type)
            @test bindingof(cst.args[2].args[1].args[2]).type == bindingof(cst.args[1])
            @test refof(cst.args[2].args[2].args[1]) == bindingof(cst.args[2].args[1].args[2])
        end
        let cst = parse_and_pass(
                """
                struct T end
                T() = 1
                        function f(x::T) x end
                        """
            )
            @test StaticLint.CoreTypes.isdatatype(bindingof(cst.args[1]).type)
            @test StaticLint.CoreTypes.isfunction(bindingof(cst.args[3]).type)
            @test bindingof(cst.args[3].args[1].args[2]).type == bindingof(cst.args[1])
            @test refof(cst.args[3].args[2].args[1]) == bindingof(cst.args[3].args[1].args[2])
        end

        let cst = parse_and_pass(
                """
                struct T end
                        t = T()
                        """
            )
            @test StaticLint.CoreTypes.isdatatype(bindingof(cst.args[1]).type)
            @test bindingof(cst.args[2].args[1]).type == bindingof(cst.args[1])
        end

        let cst = parse_and_pass(
                """
                module A
                module B
                x = 1
                end
                module C
                import ..B
                B.x
                end
                        end
                        """
            )
            @test refof(cst.args[1].args[3].args[2].args[3].args[2].args[2].args[1]) == bindingof(cst[1].args[3].args[1].args[3].args[1].args[1])
        end

        let cst = parse_and_pass(
                """
                struct T0
                    x
                end
                struct T1
                    field::T0
                end
                function f(arg::T1)
                    arg.field.x
                        end
                        """
            )
            @test refof(cst.args[3].args[2].args[1].args[1].args[1]) == bindingof(cst.args[3].args[1].args[2])
            @test refof(cst.args[3].args[2].args[1].args[1].args[2].args[1]) == bindingof(cst.args[2].args[3].args[1])
            @test refof(cst.args[3].args[2].args[1].args[2].args[1]) == bindingof(cst.args[1].args[3].args[1])
        end

        # property destructuring should infer the field's type, not the RHS type (#357)
        let cst = parse_and_pass(
                """
                struct S
                    a
                end

                struct T
                    s::S
                end

                function f1(t::T)
                    (; s) = t
                    a = s.a
                end

                function f2(t::T)
                    s = t.s
                    x = s.a
                end
                """
            )
            S = cst.meta.scope.names["S"]
            @test cst.meta.scope.names["f1"].val.meta.scope.names["s"].type == S
            @test cst.meta.scope.names["f2"].val.meta.scope.names["s"].type == S
        end

        let cst = parse_and_pass("""raw\"whatever\"""")
            @test refof(cst.args[1].args[1]) !== nothing
        end

        let cst = parse_and_pass(
                """
                macro mac_str() end
                mac"whatever"
                """
            )
            @test refof(cst.args[2].args[1]) == bindingof(cst.args[1])
        end

        let cst = parse_and_pass("[i * j for i = 1:10 for j = i:10]")
            @test refof(cst.args[1].args[1].args[1].args[1].args[2].args[2].args[2]) == bindingof(cst.args[1].args[1].args[1].args[2].args[1])
        end

        let cst = parse_and_pass("[i * j for i = 1:10, j = 1:10 for k = i:10]")
            @test refof(cst.args[1].args[1].args[1].args[1].args[2].args[2].args[2]) == bindingof(cst.args[1].args[1].args[1].args[2].args[1])
        end

        let cst = parse_and_pass(
                """
                module Reparse
                end
                using .Reparse, CSTParser
                """
            )
            @test refof(cst.args[2].args[1].args[2]).val == bindingof(cst[1])
        end

        let cst = parse_and_pass(
                """
                module A
                A
                end
                """
            )
            @test scopeof(cst).names["A"] == scopeof(cst.args[1]).names["A"]
            @test refof(cst.args[1].args[2]) == bindingof(cst.args[1])
            @test refof(cst.args[1].args[3].args[1]) == bindingof(cst.args[1])
        end
        # let cst = parse_and_pass("""
        #     using Test: @test
        #     """)
        #     @test bindingof(cst[1][4]) !== nothing
        # end
        let cst = parse_and_pass(
                """
                sin(1,2,3)
                """
            )
            @test errorof(cst.args[1]) === StaticLint.IncorrectCallArgs
        end
        let cst = parse_and_pass(
                """
                for i in length(1) end
                for i in 1.1 end
                for i in 1 end
                for i in 1:1 end
                """
            )
            @test errorof(cst.args[1].args[1]) === StaticLint.IncorrectIterSpec
            @test errorof(cst.args[2].args[1]) === StaticLint.IncorrectIterSpec
            @test errorof(cst.args[3].args[1]) === StaticLint.IncorrectIterSpec
            @test errorof(cst.args[4].args[1]) === nothing
        end

        let cst = parse_and_pass(
                """
                [i for i in length(1) end]
                [i for i in 1.1 end]
                [i for i in 1 end]
                [i for i in 1:1 end]
                """
            )
            @test errorof(cst[1][2][3]) === StaticLint.IncorrectIterSpec
            @test errorof(cst[2][2][3]) === StaticLint.IncorrectIterSpec
            @test errorof(cst[3][2][3]) === StaticLint.IncorrectIterSpec
            @test errorof(cst[4][2][3]) === nothing
        end

        let cst = parse_and_pass(
                """
                function f(x::Int)
                    for i in x
                        println(i)
                    end
                end
                """
            )
            @test errorof(cst[1][3][1][2]) === StaticLint.IncorrectIterSpec
        end

        let cst = parse_and_pass(
                """
                function f(x::Number)
                    for i in x
                        println(i)
                    end
                end
                """
            )
            @test errorof(cst[1][3][1][2]) === StaticLint.IncorrectIterSpec
        end

        let cst = parse_and_pass(
                """
                x = 3
                for i in x
                    println(i)
                end
                """
            )
            @test errorof(cst[2][2]) === StaticLint.IncorrectIterSpec
        end

        let cst = parse_and_pass(
                """
                x = 3.2
                for i in x
                    println(i)
                end
                """
            )
            @test errorof(cst[2][2]) === StaticLint.IncorrectIterSpec
        end
        let cst = parse_and_pass(
                """
                x::Float64 = 3.2 * 2
                for i in x
                    println(i)
                end
                """
            )
            @test errorof(cst[2][2]) === StaticLint.IncorrectIterSpec
        end

        for cst in parse_and_pass.(["a == nothing", "nothing == a"])
            @test errorof(cst[1][2]) === StaticLint.NothingEquality
        end
        for cst in parse_and_pass.(["a != nothing", "nothing != a"])
            @test errorof(cst[1][2]) === StaticLint.NothingNotEq
        end

        let cst = parse_and_pass(
                """
                struct Graph
                    children:: T
                end

                function test()
                    g = Graph()
                    f = g.children
                end"""
            )
            @test cst.args[2].args[2].args[2].args[2].args[2].args[1] in bindingof(cst.args[1].args[3].args[1]).refs
        end

        let cst = parse_and_pass(
                """
                __source__
                __module__
                macro m()
                    __source__
                    __module__
                end"""
            )
            @test refof(cst[1]) === nothing
            @test refof(cst[2]) === nothing
            @test refof(cst[3][3][1]) !== nothing
            @test refof(cst[3][3][2]) !== nothing
        end

        let cst = parse_and_pass(
                """
                struct Foo
                    x::DataType
                    y::Float64
                end
                (;x, y) = Foo(1,2)
                x
                y
                """
            )
            mx = cst.args[3].meta
            @test mx.ref.type.name.name.name == :DataType
            my = cst.args[4].meta
            @test my.ref.type.name.name.name == :Float64
        end
    end

    @testset "macros" begin
        @test check_resolved(
            """
            @enum(E,a,b)
            E
            a
            b
            """
        ) == [true, true, true, true, true, true, true]
    end

    @test check_resolved(
        """
        @enum E a b
        E
        a
        b
        """
    ) == [true, true, true, true, true, true, true]

    @test check_resolved(
        """
        @enum E begin
            a
            b
        end
        E
        a
        b
        """
    ) == [true, true, true, true, true, true, true]
end

@testitem "tuple args" setup = [SLSetup] begin
    let cst = parse_and_pass(
            """
            function f((arg1, arg2))
                arg1, arg2
            end"""
        )
        @test StaticLint.hasref(cst[1][3][1][1])
        @test StaticLint.hasref(cst[1][3][1][3])
    end

    let cst = parse_and_pass(
            """
            function f((arg1, arg2) = (1,2))
                arg1, arg2
            end"""
        )
        @test StaticLint.hasref(cst[1][3][1][1])
        @test StaticLint.hasref(cst[1][3][1][3])
    end

    let cst = parse_and_pass(
            """
            function f((arg1, arg2)::Tuple{Int,Int})
                arg1, arg2
            end"""
        )
        @test StaticLint.hasref(cst[1][3][1][1])
        @test StaticLint.hasref(cst[1][3][1][3])
    end
end

@testitem "type params check" setup = [SLSetup] begin
    let cst = parse_and_pass(
            """
            f() where T
            f() where {T,S}
            f() where {T<:Any}
            """
        )
        @test StaticLint.errorof(cst.args[1].args[2]) == StaticLint.UnusedTypeParameter
        @test StaticLint.errorof(cst.args[2].args[2]) == StaticLint.UnusedTypeParameter
        @test StaticLint.errorof(cst.args[2].args[3]) == StaticLint.UnusedTypeParameter
        @test StaticLint.errorof(cst.args[3].args[2]) == StaticLint.UnusedTypeParameter
    end
    let cst = parse_and_pass(
            """
            f(x::T) where T
            f(x::T,y::S) where {T,S}
            f(x::T) where {T<:Any}
            """
        )
        @test !StaticLint.haserror(cst.args[1].args[2])
        @test !StaticLint.haserror(cst.args[2].args[2])
        @test !StaticLint.haserror(cst.args[2].args[3])
        @test !StaticLint.haserror(cst.args[3].args[2])
    end
end


@testitem "overwrites_imported_function" setup = [SLSetup] begin
    let cst = parse_and_pass(
            """
            import Base:sin
            using Base:cos
            sin(x) = 1
            cos(x) = 1
            Base.tan(x) = 1
            """
        )
        @test StaticLint.overwrites_imported_function(refof(cst[3][1][1]))
        @test !StaticLint.overwrites_imported_function(refof(cst[4][1][1]))
        @test StaticLint.overwrites_imported_function(refof(cst[5][1][1][3][1]))
    end
end

@testitem "pirates" setup = [SLSetup] begin
    let cst = parse_and_pass(
            """
            import Base:sin
            struct T end
            sin(x::Int) = 1
            sin(x::T) = 1
            sin(x::Array{T}) = 1
            """
        )
        StaticLint.check_for_pirates(cst.args[3])
        StaticLint.check_for_pirates(cst.args[4])
        @test errorof(cst.args[3]) === StaticLint.TypePiracy
        @test errorof(cst.args[4]) === nothing
    end
    let cst = parse_and_pass(
            """
            struct AreaIterator{T}
                array::AbstractMatrix{T}
                radius::Int
            end
            Base.eltype(::Type{AreaIterator{T}}) where T = Tuple{T, AbstractVector{T}}
            """
        )
        StaticLint.check_for_pirates(cst[2])
        @test errorof(cst[2]) === nothing
    end
    let cst = parse_and_pass(
            """
            import Base:sin
            abstract type T end
            sin(x::Array{T}) = 1
            sin(x::Array{<:T}) = 1
            sin(x::Array{Number}) = 1
            sin(x::Array{<:Number}) = 1
            """
        )
        @test errorof(cst[3]) === nothing
        @test errorof(cst[4]) === nothing
        @test errorof(cst[5]) === StaticLint.TypePiracy
        @test errorof(cst[6]) === StaticLint.TypePiracy
    end
    let cst = parse_and_pass(
            """
            abstract type At end
            struct Ty end
            Base.eltype(::Type{Ty{T}} where {T}) = 1
            Base.length(s::Ty{T} where T <: At) = 1
            """
        )
        @test StaticLint.check_for_pirates(cst[3]) === nothing
        @test StaticLint.check_for_pirates(cst[4]) === nothing
    end

    let cst = parse_and_pass(
            """
            !=(a,b) = true
            Base.:!=(a,b) = true
            !=(a::T,b::T) = true
            !=(a::T,b::T) where T= true
            """
        )
        @test errorof(cst[1]) === StaticLint.NotEqDef
        @test errorof(cst[2]) === StaticLint.NotEqDef
        @test errorof(cst[3]) === StaticLint.NotEqDef
        @test errorof(cst[4]) === StaticLint.NotEqDef
    end

    let cst = parse_and_pass(
            """
            import Base:sin
            sin(x::Array{Number}) where {S} = 1
            sin(x::Array{Number}) where {S} where {R} = 1
            sin(x::Array{Number}) where {S} where {R} where {Q} = 1
            """
        )
        @test errorof(cst[2]) === StaticLint.TypePiracy
        @test errorof(cst[3]) === StaticLint.TypePiracy
        @test errorof(cst[4]) === StaticLint.TypePiracy
    end
end

@testitem "check_call" setup = [SLSetup] begin
    let cst = parse_and_pass(
            """
            sin(1)
            sin(1,2)
            """
        )
        @test StaticLint.errorof(cst.args[1]) === nothing
        @test StaticLint.errorof(cst.args[2]) == StaticLint.IncorrectCallArgs
    end

    let cst = parse_and_pass(
            """
            Base.sin(a,b) = 1
            function Base.sin(a,b)
                1
            end
            """
        )
        @test StaticLint.errorof(cst.args[1].args[1]) === nothing
        @test StaticLint.errorof(cst.args[2].args[1]) === nothing
    end

    let cst = parse_and_pass(
            """
            f(x) = 1
            f(1, 2)
            """
        )
        @test StaticLint.errorof(cst.args[2]) === StaticLint.IncorrectCallArgs
    end

    let cst = parse_and_pass(
            """
            view([1], 1, 2, 3)
            """
        )
        @test StaticLint.errorof(cst.args[1]) === nothing
    end

    let cst = parse_and_pass(
            """
            f(a...) = 1
            f(1)
            f(1, 2)
            """
        )
        @test StaticLint.errorof(cst.args[2]) === nothing
        @test StaticLint.errorof(cst.args[3]) === nothing
    end
    let cst = parse_and_pass(
            """
            function func(a, b)
                func(a...)
            end
            """
        )
        m_counts = StaticLint.func_nargs(cst.args[1], server.external_env)
        call_counts = StaticLint.call_nargs(cst.args[1].args[2].args[1])
        @test StaticLint.errorof(cst.args[1].args[2].args[1]) === nothing
    end
    let cst = parse_and_pass(
            """
            function func(@nospecialize args...) end
            func(1, 2)
            """
        )
        @test StaticLint.func_nargs(cst.args[1], server.external_env) == (0, typemax(Int), String[], false)
        @test StaticLint.errorof(cst.args[2]) === nothing
    end
    let cst = parse_and_pass(
            """
            argtail(x, rest...) = 1
            tail(x::Tuple) = argtail(x...)
            """
        )
        @test StaticLint.func_nargs(cst[1], server.external_env) == (1, typemax(Int), String[], false)
        @test StaticLint.errorof(cst[2]) === nothing
    end
    let cst = parse_and_pass(
            """
            func(arg::Vararg{T,N}) where N = arg
            func(a,b)
            """
        )

        @test StaticLint.func_nargs(cst[1], server.external_env) == (0, typemax(Int), String[], false)
        @test StaticLint.errorof(cst[2]) === nothing
    end

    # Mirror of the MethodStore-side handling: bounded `Vararg{T,N}`
    # in a source-defined method must contribute exactly N to the
    # arity and reject the wrong number of args.

    # func_nargs(::EXPR) — bounded contributes exactly N, parametric/
    # unbounded stay at typemax, regular args unchanged.
    for (src, expected) in [
        ("f(x::Vararg{Int,0}) = x",               (0, 0)),
        ("f(x::Vararg{Int,1}) = x",               (1, 1)),
        ("f(x::Vararg{Int,3}) = x",               (3, 3)),
        ("f(x::Vararg{Int})   = x",               (0, typemax(Int))),
        ("f(x::Int...)        = x",               (0, typemax(Int))),
        ("h(p::Int, x::Vararg{Int,2}) = (p, x)",  (3, 3)),
        ("g(y::Int) = y",                         (1, 1)),
    ]
        cst = CSTParser.parse(src)
        got = StaticLint.func_nargs(cst, server.external_env)
        @test (got[1], got[2]) == expected
    end

    # Full lint pipeline — bounded arity mismatches must flag
    # IncorrectCallArgs; matching arities and unbounded varargs
    # must stay clean.
    for (src, expected) in [
        ("f(x::Vararg{Int,3}) = x\nf(1,2,3)"   => nothing),
        ("f(x::Vararg{Int,3}) = x\nf(1,2)"     => StaticLint.IncorrectCallArgs),
        ("f(x::Vararg{Int,3}) = x\nf()"        => StaticLint.IncorrectCallArgs),
        ("f(x::Vararg{Int,3}) = x\nf(1,2,3,4)" => StaticLint.IncorrectCallArgs),
        ("f(x::Vararg{Int,0}) = x\nf()"        => nothing),
        ("f(x::Vararg{Int,0}) = x\nf(1)"       => StaticLint.IncorrectCallArgs),
        ("h(p::Int, x::Vararg{Int,2}) = (p, x)\nh(1,2,3)" => nothing),
        ("h(p::Int, x::Vararg{Int,2}) = (p, x)\nh(1)"     => StaticLint.IncorrectCallArgs),
    ]
        cst = parse_and_pass(src)
        @test StaticLint.errorof(cst.args[2]) === expected
    end

    for src in [
        "function f end\nf(1)",
        "function f end\nf()",
        "function f end\nf(1, 2, 3)",
    ]
        cst = parse_and_pass(src)
        @test StaticLint.errorof(cst.args[2]) === StaticLint.FunctionHasNoMethods
    end

    let cst = parse_and_pass("function f end\nf(x) = x\nf(1)")
        @test StaticLint.errorof(cst.args[3]) === nothing
    end

    let cst = parse_and_pass("function f end\nf(x) = x\nf(1, 2, 3)")
        @test StaticLint.errorof(cst.args[3]) === StaticLint.IncorrectCallArgs
    end

    let cst = parse_and_pass(
            """
            function f(a, b; kw = kw) end
            f(1,2, kw = 1)
            """
        )
        @test StaticLint.errorof(cst[2]) === nothing
    end
    let cst = parse_and_pass(
            """
            func(a,b,c,d) = 1
            func(a..., 2)
            """
        )
        StaticLint.call_nargs(cst[2])
        @test StaticLint.errorof(cst[2]) === nothing
    end
    let cst = parse_and_pass(
            """
            @kwdef struct A
                x::Float64
            end
            A(x = 5.0)
            """
        )
        @test StaticLint.errorof(cst[2]) === nothing
    end
    if VERSION >= v"1.10"
        let cst = parse_and_pass(
                """
                @kwdef mutable struct A
                    const x::Float64
                end
                A(x = 5.0)
                """
            )
            @test StaticLint.errorof(cst[2]) === nothing
        end
        let cst = parse_and_pass(
                """
                @kwdef mutable struct A
                    const x::Float64 = 1.0
                end
                A(x = 5.0)
                """
            )
            @test StaticLint.errorof(cst[2]) === nothing
        end
    end
    let cst = parse_and_pass(
            """
            import Base: sin
            \"\"\"
            docs
            \"\"\"
            sin
            sin(a,b) = 1
            sin(1)
            """
        )
        # Checks that documented symbols are skipped
        @test isempty(StaticLint.collect_hints(cst, StaticLint.getenv(server.files[""], server)))
    end
    let cst = parse_and_pass(
            """
            import Base: sin
            sin(a,b) = 1
            sin(1)
            """
        )
        # Checks that documented symbols are skipped
        @test isempty(StaticLint.collect_hints(cst, getenv(server.files[""], server)))
    end
    let cst = parse_and_pass(
            """
            function f(a::F)::Bool where {F} a end
            """
        )
        # ensure we strip all type decl code from around signature
        @test isempty(StaticLint.collect_hints(cst, getenv(server.files[""], server)))
    end

    # Bounded `Vararg{T,N}` consumes exactly N args. The old
    # MethodStore handling treated every Vararg as unbounded
    # (max=typemax, accept any count). Now both arity (func_nargs)
    # and signature matching (match_method) must honour `.N` when
    # it's an Integer.

    int = SymbolServer.FakeTypeName(SymbolServer.VarRef(SymbolServer.VarRef(nothing, :Core), :Int64), Any[])
    any_t = SymbolServer.FakeTypeName(SymbolServer.VarRef(SymbolServer.VarRef(nothing, :Core), :Any), Any[])
    mk(sig) = SymbolServer.MethodStore(:f, :M, "/tmp/M.jl", Int32(1), sig, Symbol[], any_t)

    m_bound = mk(Pair{Any,Any}[:x => SymbolServer.FakeTypeofVararg(int, 3)])
    m_unb   = mk(Pair{Any,Any}[:x => SymbolServer.FakeTypeofVararg(int)])
    m_pref  = mk(Pair{Any,Any}[:p => int, :x => SymbolServer.FakeTypeofVararg(int, 2)])

    # func_nargs: bounded → exact, unbounded → typemax
    @test StaticLint.func_nargs(m_bound) == (3, 3,            Symbol[], false)
    @test StaticLint.func_nargs(m_unb)   == (0, typemax(Int), Symbol[], false)
    @test StaticLint.func_nargs(m_pref)  == (3, 3,            Symbol[], false)

    # match_method: bounded rejects wrong arity, accepts only exact.
    env = StaticLint.ExternalEnv(SymbolServer.EnvStore(),
                                    Dict{SymbolServer.VarRef,Vector{SymbolServer.VarRef}}(), Symbol[])
    mm(args, m) = StaticLint.match_method(Any[args...], Any[], m, env)

    @test mm((),                          m_bound) == false
    @test mm((int, int),                  m_bound) == false
    @test mm((int, int, int),             m_bound) == true
    @test mm((int, int, int, int),        m_bound) == false

    # Unbounded behaviour preserved (also fixes a latent bug where
    # length(args) > nfixed used to spuriously return false).
    @test mm((),                          m_unb)   == true
    @test mm((int, int),                  m_unb)   == true
    @test mm((int, int, int, int, int),   m_unb)   == true

    @test mm((int,),                      m_pref)  == false
    @test mm((int, int, int),             m_pref)  == true
    @test mm((int, int, int, int),        m_pref)  == false

    # The unbounded-vararg branch of match_method must still filter
    # the trailing slots by `T`. Pins down: a `String` arg passed
    # where a `Vararg{Int}` is expected fails to match. Requires a
    # populated env so `_super` can walk Int64's supertype chain
    # (the equal-type fast path in `_type_compare` would not
    # exercise this).

    env = StaticLint.getenv(server.files[""], server)
    store = env.symbols

    int_dt = SymbolServer.stdlibs[:Core][:Int64]
    str_dt = SymbolServer.stdlibs[:Core][:String]
    any_dt = SymbolServer.stdlibs[:Core][:Any]
    int_ft = SymbolServer.FakeTypeName(SymbolServer.VarRef(SymbolServer.VarRef(nothing, :Core), :Int64), Any[])

    # f(a, b::Int...)
    m = SymbolServer.MethodStore(:f, :M, "/tmp/M.jl", Int32(1),
                    Pair{Any,Any}[:a => any_dt, :b => SymbolServer.FakeTypeofVararg(int_ft)],
                    Symbol[], any_dt)
    mm(args) = StaticLint.match_method(Any[args...], Any[], m, store)

    # Prefix is `::Any`, so anything matches the first slot.
    @test mm((int_dt,))                            == true
    @test mm((str_dt,))                            == true
    @test mm(())                                   == false   # under-arg vs fixed prefix

    # All-Int vararg tail matches.
    @test mm((int_dt, int_dt, int_dt))             == true
    @test mm((str_dt, int_dt, int_dt))             == true    # prefix Any accepts String

    # Type mismatch in the vararg tail must reject.
    @test mm((int_dt, str_dt))                     == false
    @test mm((int_dt, str_dt, str_dt))             == false
    @test mm((int_dt, int_dt, str_dt))             == false

    # Source-defined methods reach the EXPR `match_method` path,
    # which also filters trailing-slot types now. find_methods
    # rejects the call whose vararg tail doesn't intersect T.
    for (src, expect_matches) in [
        # splat `b::Int...`
        ("f(a, b::Int...) = a\nf(1, 2, 3)"          => 1),
        ("f(a, b::Int...) = a\nf(1, \"a\", \"b\")"  => 0),
        ("f(a, b::Int...) = a\nf()"                  => 0),
        # explicit unbounded `::Vararg{Int}`
        ("h(x::Vararg{Int}) = x\nh(1,2,3)"           => 1),
        ("h(x::Vararg{Int}) = x\nh(\"a\",\"b\")"     => 0),
        # bounded `::Vararg{String,2}`
        ("g(x::Vararg{String,2}) = x\ng(\"a\",\"b\")" => 1),
        ("g(x::Vararg{String,2}) = x\ng(1,2)"        => 0),
        ("g(x::Vararg{String,2}) = x\ng(\"a\")"      => 0),
        # parametric `Vararg{T,N} where {T,N}` — element type is
        # an unbound typevar, so the trailing-slot type degrades
        # to Any and any call shape is accepted.
        ("k(x::Vararg{T,N}) where {T,N} = x\nk(1,2)"       => 1),
        ("k(x::Vararg{T,N}) where {T,N} = x\nk(\"a\",\"b\")" => 1),
    ]
        cst = parse_and_pass(src)
        ms = StaticLint.find_methods(cst.args[2], StaticLint.getenv(server.files[""], server).symbols)
        @test length(ms) == expect_matches
    end

    # The lint warning ("Possible method call error") now also
    # checks types — a type mismatch in a vararg tail trips
    # `IncorrectCallArgs` even when arity matches.
    let cst = parse_and_pass("f(a, b::Int...) = a\nf(1, \"a\", \"b\")")
        @test StaticLint.errorof(cst.args[2]) === StaticLint.IncorrectCallArgs
    end
    # #335: a default positional argument makes the definition's signature read
    # like a call with a keyword arg, so the self-signature match falls back to
    # comparing against the stripped signature. This must strip *all* `where`
    # clauses, regardless of nesting depth.
    let cst = parse_and_pass(
            """
            f1(c::TT=[1,1]) where {TT<:AbstractVector{T}} where {T} = (c,TT,T)
            f2(c::TT=[1,1]) where {TT<:AbstractVector} = (c,TT)
            f3(c::TT) where {TT<:AbstractVector{T}} where {T} = (c,TT,T)
            f4(c::TT=[1,1]) where {TT<:AbstractArray{T,N}} where {T} where {N} = (c,TT,T,N)
            """
        )
        has_callargs_err(x) = StaticLint.errorof(x) === StaticLint.IncorrectCallArgs
        @test find_first(cst[1], has_callargs_err) === nothing
        @test find_first(cst[2], has_callargs_err) === nothing
        @test find_first(cst[3], has_callargs_err) === nothing
        @test find_first(cst[4], has_callargs_err) === nothing
    end
end

@testitem "check_modulename" setup = [SLSetup] begin
    let cst = parse_and_pass(
            """
            module Mod1
            module Mod11
            end
            end
            module Mod2
            module Mod2
            end
            end
            """
        )
        StaticLint.check_modulename(cst.args[1])
        StaticLint.check_modulename(cst.args[1].args[3].args[1])
        StaticLint.check_modulename(cst.args[2])
        StaticLint.check_modulename(cst.args[2].args[3].args[1])

        @test StaticLint.errorof(cst.args[1].args[2]) === nothing
        @test StaticLint.errorof(cst.args[1].args[3].args[1].args[2]) === nothing
        @test StaticLint.errorof(cst.args[2].args[2]) === nothing
        @test StaticLint.errorof(cst.args[2].args[3].args[1].args[2]) === StaticLint.InvalidModuleName
    end
end

@testitem "non-std var syntax" setup = [SLSetup] begin
    VERSION < v"1.3" && return
    let cst = parse_and_pass(
            """
            var"name" = 1
            var"func"(arg) = arg
            function var"func1"() end
            name
            func
            func1
            struct AnyType
                var"anything"
            end
            anything(x::AnyType) = x.var"anything"
            """
        )
        StaticLint.collect_hints(cst, getenv(server.files[""], server))
        @test all(n in keys(cst.meta.scope.names) for n in ("name", "func"))
        @test StaticLint.hasref(cst[4])
        @test StaticLint.hasref(cst[5])
        @test StaticLint.hasref(cst[6])
        @test cst.args[8].args[2].args[1].args[2].args[1] in bindingof(cst.args[7].args[3].args[1]).refs
    end
end

@testitem "JuMP macros" setup = [SLSetup] begin
    if false # Not to be run, requires JuMP
        let cst = parse_and_pass(
                """
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
                """
            )
            @test isempty(StaticLint.collect_hints(cst, getenv(server.files[""], server)))
        end

        let cst = parse_and_pass(
                """
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
                """
            )
            @test isempty(StaticLint.collect_hints(cst, getenv(server.files[""], server)))
        end

        let cst = parse_and_pass(
                """
                using JuMP
                model = Model()
                some_bound = 1
                @variable(model, some_bound >= x7)
                """
            )
            @test !StaticLint.hasref(cst[4][5][3])
        end

        let cst = parse_and_pass(
                """
                using JuMP
                model = Model()
                some_bound = 1
                @expression(model, ex, some_bound >= 1)
                """
            )
            @test isempty(StaticLint.collect_hints(cst, getenv(server.files[""], server)))
        end

        let cst = parse_and_pass(
                """
                using JuMP
                model = Model()
                @expression(model, expr, 1 == 1)
                @constraint(model, con1, expr)
                @constraint model con2 expr
                """
            )
            @test isempty(StaticLint.collect_hints(cst, getenv(server.files[""], server)))
        end
    end
end

@testitem "stdcall" setup = [SLSetup] begin
    let cst = parse_and_pass(
            """
            ccall(:GetCurrentProcess, stdcall, Ptr{Cvoid}, ())"""
        )
        StaticLint.collect_hints(cst, getenv(server.files[""], server))
        @test isempty(StaticLint.collect_hints(cst, getenv(server.files[""], server)))
    end
    let cst = parse_and_pass(
            """
            stdcall
            """
        )
        @test !StaticLint.hasref(cst[1])
    end
end

@testitem "check_if_conds" setup = [SLSetup] begin
    let cst = parse_and_pass(
            """
            if true end
            """
        )
        StaticLint.check_if_conds(cst.args[1])
        @test cst.args[1].args[1].meta.error == StaticLint.ConstIfCondition
    end
    let cst = parse_and_pass(
            """
            if x = 1 end
            """
        )
        StaticLint.check_if_conds(cst.args[1])
        @test cst.args[1].args[1].meta.error == StaticLint.EqInIfConditional
    end
    let cst = parse_and_pass(
            """
            if a || x = 1 end
            """
        )
        StaticLint.check_if_conds(cst.args[1])
        @test cst.args[1].args[1].meta.error == StaticLint.EqInIfConditional
    end
    let cst = parse_and_pass(
            """
            if x = 1 && b end
            """
        )
        StaticLint.check_if_conds(cst.args[1])
        @test cst.args[1].args[1].meta.error == StaticLint.EqInIfConditional
    end
end


@testitem "check_farg_unused" setup = [SLSetup] begin
    let cst = parse_and_pass("function f(arg1, arg2) arg1 end")
        StaticLint.check_farg_unused(cst[1])
        @test StaticLint.errorof(CSTParser.get_sig(cst[1])[3]) === nothing
        @test StaticLint.errorof(CSTParser.get_sig(cst[1])[5]) === StaticLint.UnusedFunctionArgument
    end
    let cst = parse_and_pass("function f(arg1::T, arg2::T) arg1 end")
        StaticLint.check_farg_unused(cst[1])
        @test StaticLint.errorof(CSTParser.get_sig(cst[1])[3]) === nothing
        @test StaticLint.errorof(CSTParser.get_sig(cst[1])[5]) === StaticLint.UnusedFunctionArgument
    end
    let cst = parse_and_pass("function f(arg1, arg2::T, arg3 = 1, arg4::T = 1) end")
        StaticLint.check_farg_unused(cst.args[1])
        @test StaticLint.errorof(CSTParser.get_sig(cst.args[1]).args[2]) === StaticLint.UnusedFunctionArgument
        @test StaticLint.errorof(CSTParser.get_sig(cst.args[1]).args[3]) === StaticLint.UnusedFunctionArgument
        @test StaticLint.errorof(CSTParser.get_sig(cst.args[1]).args[4].args[1]) === StaticLint.UnusedFunctionArgument
        @test StaticLint.errorof(CSTParser.get_sig(cst.args[1]).args[5].args[1]) === StaticLint.UnusedFunctionArgument
    end
    let cst = parse_and_pass("function f(arg) arg = 1 end")
        StaticLint.check_farg_unused(cst[1])
        @test StaticLint.errorof(CSTParser.get_sig(cst[1])[3]) === StaticLint.UnusedFunctionArgument
    end
    let cst = parse_and_pass(
            """function f(arg)
                x = arg
                arg = x
            end"""
        )
        StaticLint.check_farg_unused(cst[1])
        @test StaticLint.errorof(CSTParser.get_sig(cst[1])[3]) === nothing
    end
    let cst = parse_and_pass("function f(arg) 1 end")
        StaticLint.check_farg_unused(cst[1])
        @test StaticLint.errorof(CSTParser.get_sig(cst[1])[3]) === nothing
    end
    let cst = parse_and_pass("f(arg) = true")
        StaticLint.check_farg_unused(cst[1])
        @test StaticLint.errorof(CSTParser.get_sig(cst[1])[3]) === nothing
    end
    let cst = parse_and_pass("func(@nospecialize(arg)) = arg")
        StaticLint.check_farg_unused(cst[1])
        @test cst[1].args[1].args[2].meta.error === nothing
    end
    let cst = parse_and_pass(
            """
            function f(x,y,z)
                @. begin
                    x = z
                    y = z
                end
            end
            """
        )
        StaticLint.check_farg_unused(cst[1])
        @test StaticLint.errorof(CSTParser.get_sig(cst[1])[3]) === nothing
        @test StaticLint.errorof(CSTParser.get_sig(cst[1])[5]) === nothing
    end
    # #330: an underscore (or otherwise skipped) argument must not stop
    # subsequent arguments from being checked.
    let cst = parse_and_pass("function f(_, y)\n    return\nend")
        StaticLint.check_farg_unused(cst[1])
        @test StaticLint.errorof(CSTParser.get_sig(cst[1])[3]) === nothing
        @test StaticLint.errorof(CSTParser.get_sig(cst[1])[5]) === StaticLint.UnusedFunctionArgument
    end
    let cst = parse_and_pass("function f(x, _, z)\n    return\nend")
        StaticLint.check_farg_unused(cst[1])
        @test StaticLint.errorof(CSTParser.get_sig(cst[1])[3]) === StaticLint.UnusedFunctionArgument
        @test StaticLint.errorof(CSTParser.get_sig(cst[1])[5]) === nothing
        @test StaticLint.errorof(CSTParser.get_sig(cst[1])[7]) === StaticLint.UnusedFunctionArgument
    end
end

@testitem "check redefinition of const" setup = [SLSetup] begin
    let cst = parse_and_pass(
            """
            T = 1
            struct T end
            """
        )
        @test cst[2].meta.error == StaticLint.CannotDeclareConst
    end
    let cst = parse_and_pass(
            """
            struct T end
            T = 1
            """
        )
        @test cst[2].meta.error == StaticLint.InvalidRedefofConst
    end
    let cst = parse_and_pass(
            """
            struct T end
            T() = 1
            """
        )
        @test cst[2].meta.error === nothing
    end
end

@testitem "importing a type is not a const redefinition (#352)" setup = [SLSetup] begin
    has_error(cst, err) = any(errorof(x) === err for (_, x) in StaticLint.collect_hints(cst, getenv(server.files[""], server)))

    let cst = parse_and_pass("import Base: AbstractDict")
        @test !has_error(cst, StaticLint.InvalidRedefofConst)
    end

    let cst = parse_and_pass(
            """
            import Base: AbstractDict
            import Base: AbstractDict
            """
        )
        @test !has_error(cst, StaticLint.InvalidRedefofConst)
    end

    let cst = parse_and_pass(
            """
            using Base
            using Base: AbstractDict
            """
        )
        @test !has_error(cst, StaticLint.InvalidRedefofConst)
    end

    let cst = parse_and_pass(
            """
            import Base
            import Base: AbstractDict
            """
        )
        @test !has_error(cst, StaticLint.InvalidRedefofConst)
    end

    let cst = parse_and_pass(
            """
            using Base
            import Base: AbstractDict
            """
        )
        @test !has_error(cst, StaticLint.InvalidRedefofConst)
    end

    let cst = parse_and_pass(
            """
            import Base: AbstractDict
            const AbstractDict = 1
            """
        )
        @test has_error(cst, StaticLint.InvalidRedefofConst)
    end
end

@testitem "@testitem/@testset blocks have isolated scopes (#405)" setup = [SLSetup] begin
    has_error(cst, err) = any(errorof(x) === err for (_, x) in StaticLint.collect_hints(cst, getenv(server.files[""], server)))

    # Each @testitem runs in its own module at runtime, so reusing the same
    # const/struct names across sibling blocks must not be flagged.
    let cst = parse_and_pass(
            """
            @testitem "A" begin
                const X = 1
                struct Foo end
            end
            @testitem "B" begin
                const X = 2
                struct Foo end
            end
            """
        )
        @test scopeof(cst.args[1]) isa StaticLint.Scope
        @test scopeof(cst.args[2]) isa StaticLint.Scope
        @test scopeof(cst.args[1]) !== scopeof(cst.args[2])
        @test !has_error(cst, StaticLint.InvalidRedefofConst)
        @test !has_error(cst, StaticLint.CannotDeclareConst)
    end

    # @testset blocks evaluate in a local scope; the same isolation applies.
    let cst = parse_and_pass(
            """
            @testset "A" begin
                const X = 1
            end
            @testset "B" begin
                const X = 2
            end
            """
        )
        @test scopeof(cst.args[1]) isa StaticLint.Scope
        @test scopeof(cst.args[2]) isa StaticLint.Scope
        @test !has_error(cst, StaticLint.InvalidRedefofConst)
    end

    # A genuine redefinition *within* a single block is still reported.
    let cst = parse_and_pass(
            """
            @testitem "A" begin
                const X = 1
                const X = 2
            end
            """
        )
        @test has_error(cst, StaticLint.InvalidRedefofConst)
    end

    # References to file-level bindings still resolve from inside the block.
    let cst = parse_and_pass(
            """
            helper(x) = x
            @testitem "A" begin
                helper(1)
            end
            """
        )
        helpers = filter(x -> CSTParser.valof(x) == "helper", get_ids(cst.args[2]))
        @test length(helpers) == 1
        @test refof(helpers[1]) !== nothing
    end
end

@testitem "hoisting of inner constructors" setup = [SLSetup] begin
    let cst = parse_and_pass(
            """
            struct ASDF
                x::Int
                y::Int
                ASDF(x::Int) = new(x, 1)
            end
            ASDF(1)
            """
        )
        # Check inner constructor is hoisted
        @test isempty(StaticLint.collect_hints(cst, getenv(server.files[""], server)))
    end
end

@testitem "using statements" setup = [SLSetup] begin # e.g. `using StaticLint: StaticLint`
    let cst = parse_and_pass("using Base.Filesystem: Filesystem")
        @test StaticLint.hasref(cst.args[1].args[1].args[2].args[1])
    end
    let cst = parse_and_pass("using Base: Ordering")
        @test StaticLint.hasbinding(cst.args[1].args[1].args[2].args[1])
    end
    let cst = parse_and_pass(
            """
            module Outer
            module Inner
            x = 1
            export x
            end
            using .Inner
            end
            using .Outer: x, rand
            """
        )
        @test StaticLint.hasbinding(cst.args[2].args[1].args[2].args[1])
        @test StaticLint.hasbinding(cst.args[2].args[1].args[3].args[1])
    end
end

@testitem "don't report unknown getfields when a custom getproperty is defined" setup = [SLSetup] begin # e.g. `using StaticLint: StaticLint`
    let cst = parse_and_pass(
            """
            struct T end
            Base.getproperty(x::T, s) = 1
            T
            """
        )
        @test StaticLint.has_getproperty_method(bindingof(cst.args[1]))
        @test StaticLint.has_getproperty_method(refof(cst.args[3]))
    end
    let cst = parse_and_pass(
            """
            struct T
                f1
                f2
            end
            Base.getproperty(x::T, s) = (x,s)
            f(x::T) = x.f3
            """
        )
        @test !StaticLint.hasref(cst.args[3].args[2].args[1].args[2].args[1])
        @test isempty(StaticLint.collect_hints(cst, getenv(server.files[""], server)))
    end
    let cst = parse_and_pass(
            """
            struct T{S}
                f1
                f2
            end
            Base.getproperty(x::T{Int}, s) = (x,s)
            f(x::T) = x.f3
            """
        )
        @test !StaticLint.hasref(cst.args[3].args[2].args[1].args[2].args[1])
        @test StaticLint.is_type_of_call_to_getproperty(cst.args[2].args[1].args[2].args[2].args[1])
        @test isempty(StaticLint.collect_hints(cst, getenv(server.files[""], server)))
    end

    let cst = parse_and_pass("f(x::Module) = x.parent1")
        @test StaticLint.has_getproperty_method(server.external_env.symbols[:Core][:Module], getenv(server.files[""], server))
        @test !StaticLint.has_getproperty_method(server.external_env.symbols[:Core][:DataType], getenv(server.files[""], server))
        @test isempty(StaticLint.collect_hints(cst, getenv(server.files[""], server)))
    end
    let cst = parse_and_pass("f(x::DataType) = x.sdf")
        @test !isempty(StaticLint.collect_hints(cst, getenv(server.files[""], server)))
    end
end
@testitem "using of self" setup = [SLSetup] begin # e.g. `using StaticLint: StaticLint`
    let cst = parse_and_pass(
            """
            function f(a::rand) a end
            function f(a::Base.rand) a end
            function f(a::Int) a end
            Base.Int32(x) = 1
            function f(a::Int32) a end
            Base.fetch(x) = 1
            function f(a::fetch) a end
            """
        )
        @test errorof(cst.args[1].args[1].args[2]) === StaticLint.InvalidTypeDeclaration
        @test errorof(cst.args[2].args[1].args[2]) === StaticLint.InvalidTypeDeclaration
        @test errorof(cst.args[3].args[1].args[2]) === nothing
        @test errorof(cst.args[5].args[1].args[2]) === nothing
        @test errorof(cst.args[7].args[1].args[2]) === StaticLint.InvalidTypeDeclaration
    end

    @testset "interpret @eval" begin # e.g. `using StaticLint: StaticLint`
        let cst = parse_and_pass(
                """
                let
                    @eval adf = 1
                end
                """
            )
            @test StaticLint.scopehasbinding(scopeof(cst), "adf")
            @test !StaticLint.scopehasbinding(scopeof(cst[1]), "adf")
        end
        let cst = parse_and_pass(
                """
                let
                    @eval a,d,f = 1,2,3
                end
                """
            )
            @test StaticLint.scopehasbinding(scopeof(cst), "a")
            @test StaticLint.scopehasbinding(scopeof(cst), "d")
            @test StaticLint.scopehasbinding(scopeof(cst), "f")
            @test !StaticLint.scopehasbinding(scopeof(cst[1]), "a")
            @test !StaticLint.scopehasbinding(scopeof(cst[1]), "d")
            @test !StaticLint.scopehasbinding(scopeof(cst[1]), "f")
        end
        let cst = parse_and_pass(
                """
                let
                    @eval a = 1
                    @eval d = 2
                    @eval f = 3
                end
                """
            )
            @test StaticLint.scopehasbinding(scopeof(cst), "a")
            @test StaticLint.scopehasbinding(scopeof(cst), "d")
            @test StaticLint.scopehasbinding(scopeof(cst), "f")
            @test !StaticLint.scopehasbinding(scopeof(cst.args[1]), "a")
            @test !StaticLint.scopehasbinding(scopeof(cst.args[1]), "d")
            @test !StaticLint.scopehasbinding(scopeof(cst.args[1]), "f")
        end

        let cst = parse_and_pass(
                """
                let name = :adf
                    @eval \$name = 1
                end
                """
            )
            @test StaticLint.scopehasbinding(scopeof(cst), "adf")
            @test !StaticLint.scopehasbinding(scopeof(cst.args[1]), "adf")
        end
        let cst = parse_and_pass(
                """
                let name = [:adf]
                    @eval \$name = 1
                end
                """
            )
            @test !StaticLint.scopehasbinding(scopeof(cst), "adf")
            @test !StaticLint.scopehasbinding(scopeof(cst.args[1]), "adf")
        end

        let cst = parse_and_pass(
                """
                for name = [:adf, :asdf, :asdfs]
                    @eval \$name = 1
                end
                """
            )
            @test StaticLint.scopehasbinding(scopeof(cst), "adf")
            @test StaticLint.scopehasbinding(scopeof(cst), "asdf")
            @test StaticLint.scopehasbinding(scopeof(cst), "asdfs")
        end
        let cst = parse_and_pass(
                """
                for name = (:adf, :asdf, :asdfs)
                    @eval \$name = 1
                end
                """
            )
            @test StaticLint.scopehasbinding(scopeof(cst), "adf")
            @test StaticLint.scopehasbinding(scopeof(cst), "asdf")
            @test StaticLint.scopehasbinding(scopeof(cst), "asdfs")
        end
        let cst = parse_and_pass(
                """
                let name = :adf
                    @eval \$name(x) = 1
                end
                adf(1,2)
                """
            )
            @test StaticLint.scopehasbinding(scopeof(cst), "adf")
            @test !StaticLint.scopehasbinding(scopeof(cst.args[1]), "adf")
            @test errorof(cst.args[2]) === StaticLint.IncorrectCallArgs
        end
        let cst = parse_and_pass(
                """
                for name in (:sdf, :asdf)
                    @eval \$name(x) = 1
                end
                sdf(1,2)
                """
            )
            @test StaticLint.scopehasbinding(scopeof(cst), "sdf")
            @test !StaticLint.scopehasbinding(scopeof(cst.args[1]), "asdf")
            @test errorof(cst[2]) === StaticLint.IncorrectCallArgs
        end
    end
end

@testitem "constructor for existing type (#395)" setup = [SLSetup] begin
    invalid_type_decls(cst, env) =
        count(e -> errorof(e) === StaticLint.InvalidTypeDeclaration, e for (_, e) in StaticLint.collect_hints(cst, env))

    # Adding a constructor to an existing type via a *qualified* name extends
    # that type, so it is still understood as a datatype when used in a later
    # type declaration. (This is what e.g. MultiFloats.jl does.)
    let cst = parse_and_pass(
            """
            module M
            struct MyNumber
                sign::Bool
                exponent::Int
                mantissa::Int
            end
            function Base.BigFloat(x::MyNumber)
                x
            end
            function foo(x::BigFloat)
                x
            end
            end
            """
        )
        @test invalid_type_decls(cst, getenv(server.files[""], server)) == 0
    end

    # Same, but extending via an explicit `import` of the type.
    let cst = parse_and_pass(
            """
            module M
            import Base: BigFloat
            struct MyNumber
                sign::Bool
                exponent::Int
                mantissa::Int
            end
            function BigFloat(x::MyNumber)
                x
            end
            function cube_root(x::BigFloat)
                x
            end
            end
            """
        )
        @test invalid_type_decls(cst, getenv(server.files[""], server)) == 0
    end

    # A *bare* unqualified definition (no qualification and no import) does not
    # extend `Base.BigFloat` - it introduces a new local function that shadows
    # the type (this form is deprecated in Julia 1.12). Using the shadowing
    # name in a type declaration is therefore correctly flagged.
    let cst = parse_and_pass(
            """
            module M
            struct MyNumber
                sign::Bool
                exponent::Int
                mantissa::Int
            end
            function BigFloat(x::MyNumber)
                x
            end
            function cube_root(x::BigFloat)
                x
            end
            end
            """
        )
        @test invalid_type_decls(cst, getenv(server.files[""], server)) == 1
    end
end

@testitem "check for " setup = [SLSetup] begin # e.g. `using StaticLint: StaticLint`
    let cst = parse_and_pass(
            """
            module A
            module B
            struct T end
            end
            using .B
            function T(t::B.T)
            end
            end
            """
        )
        @test bindingof(cst.args[1].args[3].args[3]) != refof(cst.args[1].args[3].args[3].args[1].args[2].args[2].args[2].args[1])
        @test bindingof(cst.args[1].args[3].args[1].args[3].args[1]) == refof(cst.args[1].args[3].args[3][2][3][3][3][1])
    end
end
@testitem "misc" setup = [SLSetup] begin # e.g. `using StaticLint: StaticLint`
    let cst = parse_and_pass(
            """
            import Base: Bool
            function Bool(x) x end
            ^(z::Complex, n::Bool) = n ? z : one(z)
            """
        )
        @test isempty(StaticLint.collect_hints(cst, getenv(server.files[""], server)))
    end
    let cst = parse_and_pass(
            """
            (rand(d::Vector{T})::T) where {T}  =  1
            """
        )
        @test isempty(StaticLint.collect_hints(cst, getenv(server.files[""], server)))
    end
end
@testitem "Test self" setup = [SLSetup] begin
    empty!(server.files)
    f = StaticLint.loadfile(server, joinpath(@__DIR__, "..", "src", "StaticLint.jl"))
    StaticLint.semantic_pass(f)
end

@testitem "@irrational" setup = [SLSetup] begin
    let cst = parse_and_pass(
            """
            using Base:@irrational
            @irrational ase 0.45343 π
            ase
            """
        )
        @test isempty(StaticLint.collect_hints(cst, getenv(server.files[""], server)))
    end
end

@testitem "quoted getfield" setup = [SLSetup] begin
    let cst = parse_and_pass("Base.:sin")
        @test isempty(StaticLint.collect_hints(cst[1], getenv(server.files[""], server)))
    end
    @testset "quoted getfield" begin
        let cst = parse_and_pass("Base.:sin")
            @test isempty(StaticLint.collect_hints(cst.args[1], getenv(server.files[""], server)))
        end

        let cst = parse_and_pass(
                """
                sin(1,1)
                Base.sin(1,1)
                Base.:sin(1,1)
                """
            )
            @test errorof(cst.args[1]) === errorof(cst.args[2]) === errorof(cst.args[3])
        end
    end
    @testset "overloading" begin
        # overloading of a function that happens to be exported into the current scope.
        let cst = parse_and_pass(
                """
                Base.sin() = nothing
                sin()
                """
            )
            @test haskey(cst.meta.scope.names, "sin") #
            @test first(cst.meta.scope.names["sin"].refs) == server.external_env.symbols[:Base][:sin]
            @test isempty(StaticLint.collect_hints(cst[2], getenv(server.files[""], server)))
        end
        # As above but for user defined function
        let cst = parse_and_pass(
                """
                module M
                f(x) = nothing
                end
                M.f(a,b) = nothing
                M.f(1,2)
                """
            )
            @test !haskey(cst.meta.scope.names, "f")
            @test errorof(cst.args[3]) === nothing
        end

        let cst = parse_and_pass(
                """
                sin(1,1)
                Base.sin(1,1)
                Base.:sin(1,1)
                """
            )
            @test errorof(cst[1]) === errorof(cst[2]) === errorof(cst[3])
        end
    end
    # Non exported function is overloaded
    let cst = parse_and_pass(
            """
            Base.argtail() = nothing
            Base.argtail()
            """
        )
        @test !haskey(cst.meta.scope.names, "argtail") #
        @test isempty(StaticLint.collect_hints(cst, getenv(server.files[""], server)))
    end
    # As above but for user defined function
    let cst = parse_and_pass(
            """
            module M
            ff(x) = nothing
            end
            M.ff() = nothing
            M.ff()
            """
        )
        @test !haskey(cst.meta.scope.names, "ff")
        @test isempty(StaticLint.collect_hints(cst[3], getenv(server.files[""], server)))
    end

    let cst = parse_and_pass(
            """
            import Base: argtail
            Base.argtail() = nothing
            Base.argtail()
            argtail()
            """
        )
        @test cst.meta.scope.names["argtail"] === bindingof(cst[1][2][3][1])
        @test StaticLint.get_method(cst.meta.scope.names["argtail"].refs[2]) isa CSTParser.EXPR
        @test cst[3][1][3][1].meta.ref == cst.meta.scope.names["argtail"]
        @test isempty(StaticLint.collect_hints(cst, getenv(server.files[""], server)))
    end
end

@testitem "on demand resolving of export statements" setup = [SLSetup] begin
    let cst = parse_and_pass(
            """
            module TopModule
            abstract type T end
            export T
            module SubModule
            using ..TopModule
            T
            end
            end"""
        )
        @test refof(cst.args[1].args[3].args[3].args[3].args[2]) !== nothing
    end
end


@testitem "check kw default definition" setup = [SLSetup] begin
    function kw_default_ok(s)
        cst = parse_and_pass(s)
        @test errorof(cst.args[1].args[2].args[2]) === nothing
    end
    function kw_default_notok(s)
        cst = parse_and_pass(s)
        @test errorof(cst.args[1].args[2].args[2]) == StaticLint.KwDefaultMismatch
    end

    kw_default_ok("f(x::Float64 = 0.1)")
    kw_default_ok("f(x::Float64 = f())")
    kw_default_ok("f(x::Float32 = f())")
    kw_default_ok("f(x::Float32 = 3f0")
    kw_default_ok("f(x::Float32 = 3_0f0")
    kw_default_ok("f(x::Float32 = 0f00")
    kw_default_ok("f(x::Float32 = -0f02")
    kw_default_ok("f(x::Float32 = Inf32")
    kw_default_ok("f(x::Float32 = 30f3")
    kw_default_ok("f(x::String = \"1\")")
    kw_default_ok("f(x::String = f())")
    kw_default_ok("f(x::Symbol = :x")
    kw_default_ok("f(x::Symbol = f()")
    kw_default_ok("f(x::Char = 'a'")
    kw_default_ok("f(x::Bool = true")
    kw_default_ok("f(x::Bool = false")
    kw_default_ok("f(x::UInt8 = 0b0100_0010")
    kw_default_ok("f(x::UInt16 = 0b0000_0000_0000")
    kw_default_ok("f(x::UInt32 = 0b00000000000000000000000000000000")
    kw_default_ok("f(x::UInt8 = 0o000")
    kw_default_ok("f(x::UInt16 = 0o0_0_0_0_0_0")
    kw_default_ok("f(x::UInt32 = 0o000000000")
    kw_default_ok("f(x::UInt64 = 0o000_000_000_000_0")
    kw_default_ok("f(x::UInt8 = 0x0")
    kw_default_ok("f(x::UInt16 = 0x0000")
    kw_default_ok("f(x::UInt32 = 0x00000")
    kw_default_ok("f(x::UInt32 = -0x00000")
    kw_default_ok("f(x::UInt64 = 0x0000_0000_0")
    kw_default_ok("f(x::UInt128 = 0x00000000_00000000_00000000_00000000")
    kw_default_ok("f(x::UInt128 = 0x00000000_00000000_00000000_00000000")
    if Sys.WORD_SIZE == 64
        kw_default_ok("f(x::Int64 = 0")
        kw_default_ok("f(x::UInt = 0x0000_0000_0")
    else
        kw_default_ok("f(x::Int32 = 0")
        kw_default_ok("f(x::UInt = 0x0000_0")
    end
    kw_default_ok("f(x::Int = 1)")
    kw_default_ok("f(x::Int = f())")
    kw_default_ok("f(x::Int8 = Int8(0)")
    kw_default_ok("f(x::Int8 = convert(Int8,0)")

    if Sys.WORD_SIZE == 64
        kw_default_notok("f(x::Int8 = 0")
        kw_default_notok("f(x::Int16 = 0")
        kw_default_notok("f(x::Int32 = 0")
        kw_default_notok("f(x::Int64 = 0x0000_0000_0")
        kw_default_notok("f(x::Int128 = 0")
    else
        kw_default_notok("f(x::Int8 = 0")
        kw_default_notok("f(x::Int16 = 0")
        kw_default_notok("f(x::Int32 = 0x0000_0")
        kw_default_notok("f(x::Int64 = 0")
        kw_default_notok("f(x::Int128 = 0")
    end
    kw_default_notok("f(x::Int8 = 0000_0000")
    kw_default_notok("f(x::Int16 = 0000_0000")
    kw_default_notok("f(x::Int128 = 0000_0000")
    kw_default_notok("f(x::Float64 = 1)")
    kw_default_notok("f(x::Float32 = 3.4")
    kw_default_notok("f(x::Float32 = -23.")
    kw_default_notok("f(x::Int = 0.1)")
    kw_default_notok("f(x::String = 0.1)")
    kw_default_notok("f(x::Symbol = \"a\"")
    kw_default_notok("f(x::Char = \"a\"")
    kw_default_notok("f(x::Bool = 1")
    kw_default_notok("f(x::Bool = 0x01")
    kw_default_notok("f(x::UInt8 = 0b000000000")
    kw_default_notok("f(x::UInt16 = 0b0000_0000_0000_0000_0")
    kw_default_notok("f(x::UInt32 = 0b0")
    kw_default_notok("f(x::UInt64 = 0b0_0")
    kw_default_notok("f(x::UInt128 = 0b0")
    kw_default_notok("f(x::UInt8 = 0o0000")
    kw_default_notok("f(x::UInt16 = 0o0")
    kw_default_notok("f(x::UInt32 = 0o00000000000000")
    kw_default_notok("f(x::UInt64 = 0o0_0")
    kw_default_notok("f(x::UInt128 = 0o00")
    kw_default_notok("f(x::UInt8 = 0x000")
    kw_default_notok("f(x::UInt16 = 0x00000")
    kw_default_notok("f(x::UInt32 = 0x0000_00_000")
    kw_default_notok("f(x::UInt64 = 0x000_0_0")
    kw_default_notok("f(x::UInt128 = 0x000000")
end

@testitem "check_use_of_literal" setup = [SLSetup] begin
    let cst = parse_and_pass(
            """
            module \"a\" end
            abstract type \"\"\"123\"\"\" end
            primitive type 1 8 end
            struct 1.0 end
            mutable struct 'a' end
            1 = 1
            f(true = 1)
            123::123
            123 isa false
            """
        )
        @test errorof(cst.args[1].args[2]) === StaticLint.InappropriateUseOfLiteral
        @test errorof(cst.args[2].args[1]) === StaticLint.InappropriateUseOfLiteral
        @test errorof(cst.args[3].args[1]) === StaticLint.InappropriateUseOfLiteral
        @test errorof(cst.args[4].args[2]) === StaticLint.InappropriateUseOfLiteral
        @test errorof(cst.args[5].args[2]) === StaticLint.InappropriateUseOfLiteral
        @test errorof(cst.args[6].args[1]) === StaticLint.InappropriateUseOfLiteral
        @test errorof(cst.args[7].args[2].args[1]) === StaticLint.InappropriateUseOfLiteral
        @test errorof(cst.args[8].args[2]) === StaticLint.InappropriateUseOfLiteral
        @test errorof(cst.args[9].args[3]) === StaticLint.InappropriateUseOfLiteral
    end
end

@testitem "check_break_continue" setup = [SLSetup] begin
    let cst = parse_and_pass(
            """
            for i = 1:10
                continue
            end
            break
            """
        )
        @test errorof(cst.args[1].args[2].args[1]) === nothing
        @test errorof(cst.args[2]) === StaticLint.ShouldBeInALoop
    end
end

@testitem "@." setup = [SLSetup] begin
    let cst = parse_and_pass("@. a + b")
        @test StaticLint.hasref(cst.args[1].args[1])
    end
end

@testitem "using" setup = [SLSetup] begin
    cst = parse_and_pass("using Base")
    @test StaticLint.hasbinding(cst.args[1].args[1].args[1])

    cst = parse_and_pass("using Base.Meta")
    @test !StaticLint.hasbinding(cst.args[1].args[1].args[1])
    @test StaticLint.hasbinding(cst.args[1].args[1].args[2])
    @test haskey(cst.meta.scope.modules, :Meta)

    cst = parse_and_pass("using Core.Compiler.Pair")
    @test !StaticLint.hasbinding(cst.args[1].args[1].args[1])
    @test !StaticLint.hasbinding(cst.args[1].args[1].args[2])
    @test StaticLint.hasbinding(cst.args[1].args[1].args[3])

    cst = parse_and_pass("using Base.UUID, Base.any")
    @test StaticLint.hasbinding(cst.args[1].args[1].args[2])
    @test StaticLint.hasbinding(cst.args[1].args[2].args[2])

    cst = parse_and_pass("using Base.Meta: quot, lower")
    @test StaticLint.hasbinding(cst.args[1].args[1].args[2].args[1])
    @test StaticLint.hasbinding(cst.args[1].args[1].args[3].args[1])

    cst = parse_and_pass("using Base.Meta: quot, lower")
end

@testitem "issue 1609" setup = [SLSetup] begin
    let
        cst1 = parse_and_pass("function g(@nospecialize(x), y) x + y end")
        cst2 = parse_and_pass("function g(@nospecialize(x), y) y end")
        @test !StaticLint.haserror(cst1.args[1].args[1].args[2].args[3])
        @test StaticLint.haserror(cst2.args[1].args[1].args[2].args[3])
    end
end
@testitem "j-vsc issue 1835" setup = [SLSetup] begin
    let
        cst = parse_and_pass(
            """const x::T = x
            local const x = 1"""
        )
        @test errorof(cst.args[1]) === (VERSION < v"1.8.0-DEV.1500" ? StaticLint.TypeDeclOnGlobalVariable : nothing)
        @test errorof(cst.args[2]) === StaticLint.UnsupportedConstLocalVariable
    end
end

@testitem "issue 1609 (nospecialize defaults)" setup = [SLSetup] begin
    let
        cst1 = parse_and_pass("function g(@nospecialize(x), y) x + y end")
        cst2 = parse_and_pass("function g(@nospecialize(x) = 1) x end")
        cst3 = parse_and_pass("function g(@nospecialize(x) = 1, y = 2) x + y end")
        cst4 = parse_and_pass("function g(@nospecialize(x), y) y end")
        @test !StaticLint.haserror(cst1.args[1].args[1].args[2].args[3])
        @test !StaticLint.haserror(cst2.args[1].args[1].args[2].args[1])
        @test !StaticLint.haserror(cst3.args[1].args[1].args[2].args[1])
        @test StaticLint.haserror(cst4.args[1].args[1].args[2].args[3])
    end
end

@testitem "issue #390 (nospecialize without argument)" setup = [SLSetup] begin
    @test StaticLint.func_nargs(CSTParser.parse("function f(@nospecialize) end"), server.external_env) == (1, 1, Symbol[], false)
    @test StaticLint.func_nargs(CSTParser.parse("function f(@nospecialize()) end"), server.external_env) == (1, 1, Symbol[], false)
    @test StaticLint.func_nargs(CSTParser.parse("f(@nospecialize) = 1"), server.external_env) == (1, 1, Symbol[], false)
    # Full pipeline: defining and calling such a function must not crash.
    @test parse_and_pass("""
        function f(@nospecialize(x))
            @nospecialize
            return x
        end
        f(1)
        """) isa CSTParser.EXPR
end

@testitem "issue #389 (macro-rewritten call signature)" setup = [SLSetup] begin
    # An unknown macro wrapping a function definition can rewrite its call
    # signature (e.g. KernelAbstractions' `@kernel`), so calls with a differing
    # number of arguments must not be flagged as `IncorrectCallArgs`.
    let cst = parse_and_pass(
            """
            @kernel function mul2_kernel(A)
                A[I] = 2 * A[I]
            end
            mul2_kernel(dev, 64)
            """
        )
        @test errorof(cst.args[2]) === nothing
        @test StaticLint.func_nargs(cst.args[1].args[end], server.external_env) ==
            (0, typemax(Int), Symbol[], true)
    end

    # Signature-preserving Base macros (`@inline`, `Base.@propagate_inbounds`, ...)
    # resolve to known Base macros, so argument counts are still checked.
    let cst = parse_and_pass(
            """
            @inline function g(x)
                x
            end
            g(1, 2)
            """
        )
        @test errorof(cst.args[2]) === StaticLint.IncorrectCallArgs
        @test StaticLint.func_nargs(cst.args[1].args[end], server.external_env) ==
            (1, 1, Symbol[], false)
    end

    # The module-qualified form (`Base.@propagate_inbounds`) resolves too.
    let cst = parse_and_pass(
            """
            Base.@propagate_inbounds function h(a, b)
                a + b
            end
            h(1)
            """
        )
        @test errorof(cst.args[2]) === StaticLint.IncorrectCallArgs
    end
end

@testitem "issue #226" setup = [SLSetup] begin
    cst = parse_and_pass("function my_function(::Any...) end")
    @test !StaticLint.haserror(cst.args[1].args[1].args[2])
end

@testitem "issue #218" setup = [SLSetup] begin
    cst = parse_and_pass(
        """
        struct Asdf end

        function foo(x)
            if x > 0
                ret = Asdf
            else
                ret = "hello"
            end
        end

        function foo(x)
            if x > 0
                ret = Asdf()
            else
                ret = "hello"
            end
        end"""
    )
    @test errorof(cst.args[2].args[2].args[1].args[3].args[1].args[1]) !== StaticLint.InvalidRedefofConst
    @test errorof(cst.args[3].args[2].args[1].args[3].args[1].args[1]) !== StaticLint.InvalidRedefofConst
end

@testitem "issue #382" setup = [SLSetup] begin
    cst = parse_and_pass(
        """
        function f(a::T, invert=false)::T where {T <: Integer}
            invert ? -a : a
        end"""
    )
    @test !StaticLint.haserror(cst.args[1].args[1].args[1].args[1])
end

@testitem "issue #210" setup = [SLSetup] begin
    VERSION > v"1.5-" || return
    cst = parse_and_pass("""h()::@NamedTuple{a::Int,b::String} = (a=1, b = "s")""")
    @test isempty(StaticLint.collect_hints(cst, getenv(server.files[""], server)))
end
@testitem "Base.@kwdef" setup = [SLSetup] begin
    isdefined(Base, Symbol("@kwdef")) || return
    cst = parse_and_pass(
        """
        Base.@kwdef struct T
            arg = 1
        end"""
    )
    @test isempty(StaticLint.collect_hints(cst, getenv(server.files[""], server)))
end
@testitem "type inference by use" setup = [SLSetup] begin
    cst = parse_and_pass(
        """
        f(x::String) = true
        function g(x)
            f(x)
        end"""
    )
    @test bindingof(cst.args[2].args[1].args[2]).type !== nothing

    cst = parse_and_pass(
        """
        f(x::String) = true
        f(x::Char) = true
        function g(x)
            f(x)
        end"""
    )
    @test bindingof(cst.args[3].args[1].args[2]).type === nothing

    cst = parse_and_pass(
        """
        f(x::String) = true
        f1(x::String) = true
        function g(x)
            f(x)
            f1(x)
        end"""
    )
    @test bindingof(cst.args[3].args[1].args[2]).type !== nothing

    cst = parse_and_pass(
        """
        f(x::String) = true
        f1(x::Char) = true
        function g(x)
            f(x)
            f1(x)
        end"""
    )
    @test bindingof(cst.args[3].args[1].args[2]).type === nothing

    cst = parse_and_pass(
        """
        f(x::String) = true
        f1(x) = true
        function g(x)
            f(x)
            f1(x)
        end"""
    )
    @test bindingof(cst.args[3].args[1].args[2]).type !== nothing
end

# @testset "forward relative using/import" begin
#    cst = parse_and_pass("""
# module A
# module B
#     module C
#         using ..Sibling
#         f() = Sibling.g()
#     end
#     module Sibling
#         export g
#         g() = 1
#     end
# end
# end
# """)
#    # f’s body Sibling.g should resolve
#    fcall = cst.args[1].args[3].args[1].args[3].args[2]   # C’s f() definition
#    # Sibling.g call: fcall.args[2].args[1] is the call; its callee is getfield
#    callee = fcall.args[2].args[1].args[1]               # Sibling
#    @test StaticLint.hasref(callee)
# end

@testitem "forward relative using/import" setup = [SLSetup] begin
    cst = parse_and_pass(
        """
        module A
        module B
            module C
                using ..Sibling
                f() = Sibling.g()
            end
            module Sibling
                export g
                g() = 1
            end
        end
        end
        """
    )

    modC = find_module_by_name(cst, "C")
    @test modC !== nothing

    fexpr = find_first(modC) do x
        CSTParser.defines_function(x) &&
            CSTParser.isidentifier(CSTParser.get_name(x)) &&
            CSTParser.valof(CSTParser.get_name(x)) == "f"
    end
    @test fexpr !== nothing

    gget = find_first(fexpr, CSTParser.is_getfield_w_quotenode)
    @test gget !== nothing

    lhs = gget.args[1]                    # Sibling
    rhsid = gget.args[2].args[1]          # g (inside QuoteNode)

    @test StaticLint.hasref(lhs)
    @test StaticLint.hasref(rhsid)
end

@testitem "too many dots" setup = [SLSetup] begin
    cst = parse_and_pass(
        """
        module A
            import ....X
        end
        """
    )
    errs = StaticLint.collect_hints(cst, getenv(server.files[""], server))
    @test any(err -> StaticLint.errorof(err[2]) === StaticLint.RelativeImportTooManyDots, errs)
end

@testitem "add eval method to modules/toplevel scope" setup = [SLSetup] begin
    cst = parse_and_pass(
        """
        module M
        expr = :(a + b)
        eval(expr)
        end
        """
    )
    @test !StaticLint.haserror(cst.args[1].args[3].args[2])

    cst = parse_and_pass(
        """
        expr = :(a + b)
        eval(expr)
        """
    )
    @test !StaticLint.haserror(cst.args[2])
end

@testitem "reparse" setup = [SLSetup] begin
    cst = parse_and_pass(
        """
        x = 1
        function f(arg)
            x
        end
        """
    )
    @test StaticLint.hasref(cst.args[2].args[2].args[1])
    StaticLint.clear_meta(cst[2])
    @test !StaticLint.hasref(cst.args[2].args[2].args[1])
    StaticLint.semantic_pass(server.files[""], CSTParser.EXPR[cst[2]])
    @test StaticLint.hasref(cst.args[2].args[2].args[1])
end

@testitem "duplicate function argument" setup = [SLSetup] begin
    cst = parse_and_pass(
        """
        f(a,a) = a
        """
    )
    @test errorof(cst[1][1][5]) == StaticLint.DuplicateFuncArgName
end

@testitem "type alias bindings" setup = [SLSetup] begin
    cst = parse_and_pass(
        """
        T{S} = Vector{S}
        """
    )
    @test haskey(cst.meta.scope.names, "T")
    @test haskey(cst[1].meta.scope.names, "S")
end

@testitem ":call w/ :parameters traverse order" setup = [SLSetup] begin
    cst = parse_and_pass(
        """
        function f(arg; kw = arg)
            arg * kw
        end
        """
    )
    @test isempty(StaticLint.collect_hints(cst, getenv(server.files[""], server)))
end

@testitem "handle shadow bindings on method" setup = [SLSetup] begin
    cst = parse_and_pass(
        """
        f(x) = 1
        g = f
        g(1)
        """
    )
    @test isempty(StaticLint.collect_hints(cst, getenv(server.files[""], server)))
end

@testitem "documented symbol resolving" setup = [SLSetup] begin
    cst = parse_and_pass(
        """
        \"\"\"
        doc
        \"\"\"
        func
        func(x) = 1
        """
    )
    @test isempty(StaticLint.collect_hints(cst, getenv(server.files[""], server)))

    cst = parse_and_pass(
        """
        \"\"\"
        doc
        \"\"\"
        func(a,b)::Int
        func(x, b) = 1
        """
    )
    @test isempty(StaticLint.collect_hints(cst, getenv(server.files[""], server)))
end

@testitem "unused bindings" setup = [SLSetup] begin
    cst = parse_and_pass(
        """
        function f(arg, arg2)
            arg*arg2
            arg3 = 1
        end
        """
    )
    @test errorof(cst[1][3][2][1]) !== nothing

    cst = parse_and_pass(
        """
        function f()
            arg = false
            while arg
                if arg
                end
                arg = true
            end
        end
        """
    )
    @test isempty(StaticLint.collect_hints(cst, server))

    cst = parse_and_pass(
        """
        function f(arg)
            arg
            while true
                arg = 1
            end
        end
        """
    )
    @test isempty(StaticLint.collect_hints(cst, server))

    cst = parse_and_pass(
        """
        function f(arg)
            arg
            while true
                while true
                    arg = 1
                end
            end
        end
        """
    )
    @test isempty(StaticLint.collect_hints(cst, server))

    cst = parse_and_pass(
        """
        function f()
            (a = 1, b = 2)
        end
        """
    )
    @test isempty(StaticLint.collect_hints(cst, server))

    cst = parse_and_pass(
        """
        function f()
            arg = 0
            if 1
                while true
                    arg = 1
                end
            end
        end
        """
    )
    @test isempty(StaticLint.collect_hints(cst, server))
end

@testitem "unwrap sig" setup = [SLSetup] begin
    cst = parse_and_pass(
        """
        function multiply!(x::T, y::Integer) where {T} end
        multiply!(1, 3)
        """
    )
    @test errorof(cst[2]) === nothing

    cst = parse_and_pass(
        """
        function multiply!(x::T, y::Integer)::T where {T} end
        multiply!(1, 3)
        """
    )
    @test errorof(cst[2]) === nothing

    @test StaticLint.haserror(parse_and_pass("function f(z::T)::Nothing where T end")[1].args[1].args[1].args[1].args[2])
    @test StaticLint.haserror(parse_and_pass("function f(z::T) where T end")[1].args[1].args[1].args[2])
end

@testitem "clear .type refs" setup = [SLSetup] begin
    cst = parse_and_pass(
        """
        struct T end
        function f(x::T)
        end
        """
    )
    @test bindingof(cst[2][2][3]).type == bindingof(cst[1])
    StaticLint.clear_meta(cst[1])
    @test bindingof(cst[2][2][3]).type === nothing
end

@testitem "struct where-clause hints" setup = [SLSetup] begin
    cst = parse_and_pass(
        """
        struct T{S,R} where S <: Number where R <: Number
        end
        """
    )
    @test isempty(StaticLint.collect_hints(cst, server))

    cst = parse_and_pass(
        """
        struct T{S,R} <: Number where S <: Number
            x::S
        end
        """
    )
    @test isempty(StaticLint.collect_hints(cst, server))
end

@testitem "where type param infer" setup = [SLSetup] begin
    cst = parse_and_pass(
        """
        foo(u::Union) = 1
        function foo(x::T) where {T}
            x + foo(T)
        end
        """
    )

    @test cst[2].meta.scope.names["T"].type isa SymbolServer.DataTypeStore
    @test isempty(StaticLint.collect_hints(cst, server))
end

@testitem "where type param infer (multiple)" setup = [SLSetup] begin
    cst = parse_and_pass(
        """
        bar(u::Any) = 1
        foo(x::T, y::S, q::V) where {T, S <: V} where {V <: Integer} = x + y + q + bar(S) + bar(T) + bar(V)
        """
    )

    @test cst[2].meta.scope.names["T"].type isa SymbolServer.DataTypeStore
    @test cst[2].meta.scope.names["S"].type isa SymbolServer.DataTypeStore
    @test cst[2].meta.scope.names["V"].type isa SymbolServer.DataTypeStore
    @test isempty(StaticLint.collect_hints(cst, server))
end

@testitem "softscope" setup = [SLSetup] begin
    cst = parse_and_pass(
        """
        function foo()
            x = 1
            x
            if rand(Bool)
                x = 2
            end
            x
            while rand(Bool)
                x = 3
            end
            x
            for _ in 1:2
                x = 4
                y = 1
            end
            x
        end
        """
    )

    # check soft-scope bindings are lifted to parent scope
    @test refof(cst[1][3][2]) == bindingof(cst[1][3][1][1])
    @test refof(cst[1][3][4]) == bindingof(cst[1][3][3][3][1][1])
    @test refof(cst[1][3][6]) == bindingof(cst[1][3][5][3][1][1])
    @test refof(cst[1][3][8]) == bindingof(cst[1][3][7][3][1][1])

    # check binding made in soft-scope with no matching binidng in parent scope isn't lifted
    @test !haskey(scopeof(cst[1]).names, "y")
    @test haskey(scopeof(cst[1][3][7]).names, "y")


    @test length(StaticLint.loose_refs(bindingof(cst[1][3][1][1]))) == 8
    @test length(StaticLint.loose_refs(bindingof(cst[1][3][3][3][1][1]))) == 8
    @test length(StaticLint.loose_refs(bindingof(cst[1][3][5][3][1][1]))) == 8
    @test length(StaticLint.loose_refs(bindingof(cst[1][3][7][3][1][1]))) == 8

    cst = parse_and_pass(
        """
        function foo()
            for _ in 1:2
                x = 1
                x
            end
            x
            x = 1
            x
        end
        """
    )
    @test length(StaticLint.loose_refs(bindingof(cst[1][3][1][3][1][1]))) == 2
    @test length(StaticLint.loose_refs(bindingof(cst[1][3][3][1]))) == 2
end

# @testset "test workspace packages" begin
#     empty!(server.files)
#     s1 = """
#     module WorkspaceMod
#     inner_sym = 1
#     exported_sym = 1
#     export exported_sym
#     end"""
#     f1 = StaticLint.File("workspacemod.jl", s1, CSTParser.parse(s1, true), nothing, server)
#     StaticLint.setroot(f1, f1)
#     StaticLint.setfile(server, f1.path, f1)
#     StaticLint.semantic_pass(f1)
#     server.workspacepackages["WorkspaceMod"] = f1
#     s2 = """
#     using WorkspaceMod
#     exported_sym
#     WorkspaceMod.inner_sym
#     """
#     f2 = StaticLint.File("someotherfile.jl", s2, CSTParser.parse(s2, true), nothing, server)
#     StaticLint.setroot(f2, f2)
#     StaticLint.setfile(server, f2.path, f2)
#     StaticLint.semantic_pass(f2)
#     @test StaticLint.hasref(StaticLint.getcst(f2)[1][2][1])
#     @test StaticLint.hasref(StaticLint.getcst(f2)[2])
#     @test StaticLint.hasref(StaticLint.getcst(f2)[3][3][1])
# end
@testitem "#1218" setup = [SLSetup] begin
    cst = parse_and_pass(
        """function foo(a; p) a+p end
        foo(1, p = true)"""
    )
    @test isempty(StaticLint.collect_hints(cst, server))

    cst = parse_and_pass(
        """function foo(a; p) a end
        foo(1, p = true)"""
    )
    @test cst[1][2][4][1].meta.error != false

    cst = parse_and_pass(
        """function foo(a; p::Bool) a+p end
        foo(1, p = true)"""
    )
    @test isempty(StaticLint.collect_hints(cst, server))

    cst = parse_and_pass(
        """function foo(a; p::Bool) a end
        foo(1, p = true)"""
    )
    @test cst[1][2][4][1].meta.error != false
end


@testitem "import as ..." setup = [SLSetup] begin
    Meta.parse("import a as b", raise = false).head !== :error || return
    cst = parse_and_pass("""import Base as base""")
    @test StaticLint.hasbinding(cst[1][2][3])
    @test !StaticLint.hasbinding(cst[1][2][1][1])

    # incomplete expressinon should not error
    cst = parse_and_pass("""import Base as""")
end


@testitem "#1218 import into submodule" setup = [SLSetup] begin
    cst = parse_and_pass(
        """
        module Sup
        function myfunc end
        module SubA
        import ..myfunc
        myfunc(x::Int) = println("hello Int: ", x) # Cannot define function ; it already has a value.
        end # module

        end
        """
    )
    @test isempty(StaticLint.collect_hints(cst, server))

end


@testitem "macrocall bindings: #2187" setup = [SLSetup] begin
    cst = parse_and_pass(
        """
        function f(url = 1, file = 1)
            @info "Downloading" source = url dest = file
            return nothing
        end
        """
    )
    @test isempty(StaticLint.collect_hints(cst, server))
end

@testitem "aliased import: #974" setup = [SLSetup] begin
    cst = parse_and_pass(
        """
        const CC = Core.Compiler
        import .CC: div
        """
    )
    @test isempty(StaticLint.collect_hints(cst, server))

    cst = parse_and_pass(
        """
        const C = Core
        import .C: div
        """
    )
    @test isempty(StaticLint.collect_hints(cst, server))
end

@testitem "kwarg refs" setup = [SLSetup] begin
    cst = parse_and_pass(
        """
        function foo(aaa, bbb; ccc)
            return aaa + bbb + ccc
        end
        """
    )
    for (_, b) in cst.args[1].meta.scope.names
        @test length(b.refs) == 2
    end

    cst = parse_and_pass(
        """
        function foo(aaa, bbb::Foo; ccc::Bar)
            return aaa + bbb + ccc
        end
        """
    )
    for (_, b) in cst.args[1].meta.scope.names
        @test length(b.refs) == 2
    end

    cst = parse_and_pass(
        """
        function foo(aaa, bbb=1; ccc=2)
            return aaa + bbb + ccc
        end
        """
    )
    for (_, b) in cst.args[1].meta.scope.names
        @test length(b.refs) == 2
    end
    cst = parse_and_pass(
        """
        function foo(aaa, bbb::Foo=1; ccc::Bar=2)
            return aaa + bbb + ccc
        end
        """
    )
    for (_, b) in cst.args[1].meta.scope.names
        @test length(b.refs) == 2
    end
end

@testitem "iteration over 1:length(...)" setup = [SLSetup] begin
    cst = parse_and_pass("arr = []; [1 for _ in 1:length(arr)]")
    @test isempty(StaticLint.collect_hints(cst, server))
    cst = parse_and_pass("arr = []; [arr[i] for i in 1:length(arr)]")
    @test length(StaticLint.collect_hints(cst, server)) == 2
    cst = parse_and_pass("arr = []; [i for i in 1:length(arr)]")
    @test length(StaticLint.collect_hints(cst, server)) == 0

    cst = parse_and_pass(
        """
        arr = []
        for _ in 1:length(arr)
        end
        """
    )
    @test isempty(StaticLint.collect_hints(cst, server))
    cst = parse_and_pass(
        """
        arr = []
        for i in 1:length(arr)
            arr[i]
        end
        """
    )
    @test length(StaticLint.collect_hints(cst, server)) == 2
    cst = parse_and_pass(
        """
        arr = []
        for i in 1:length(arr)
            println(i)
        end
        """
    )
    @test length(StaticLint.collect_hints(cst, server)) == 0

    cst = parse_and_pass(
        """
        arr = []
        for _ in 1:length(arr), _ in 1:length(arr)
        end
        """
    )
    @test isempty(StaticLint.collect_hints(cst, server))
    cst = parse_and_pass(
        """
        arr = []
        for i in 1:length(arr), j in 1:length(arr)
            arr[i] + arr[j]
        end
        """
    )
    @test length(StaticLint.collect_hints(cst, server)) == 4
    cst = parse_and_pass(
        """
        arr = []
        for i in 1:length(arr), j in 1:length(arr)
            println(i + j)
        end
        """
    )
    @test length(StaticLint.collect_hints(cst, server)) == 0

    cst = parse_and_pass(
        """
        function f(arr::Vector)
            for i in 1:length(arr), j in 1:length(arr)
                arr[i] + arr[j]
            end
        end
        """
    )
    @test length(StaticLint.collect_hints(cst, server)) == 0

    cst = parse_and_pass(
        """
        function f(arr::Array)
            for i in 1:length(arr), j in 1:length(arr)
                arr[i] + arr[j]
            end
        end
        """
    )
    @test length(StaticLint.collect_hints(cst, server)) == 0

    cst = parse_and_pass(
        """
        function f(arr::Matrix)
            for i in 1:length(arr), j in 1:length(arr)
                arr[i] + arr[j]
            end
        end
        """
    )
    @test length(StaticLint.collect_hints(cst, server)) == 0

    cst = parse_and_pass(
        """
        function f(arr::Array{T,N}) where T where N
            for i in 1:length(arr), j in 1:length(arr)
                arr[i] + arr[j]
            end
        end
        """
    )
    @test length(StaticLint.collect_hints(cst, server)) == 0

    cst = parse_and_pass(
        """
        function f(arr::AbstractArray)
            for i in 1:length(arr), j in 1:length(arr)
                arr[i] + arr[j]
            end
        end
        """
    )
    @test length(StaticLint.collect_hints(cst, server)) == 4

    cst = parse_and_pass(
        """
        function f(arr)
            for i in 1:length(arr), j in 1:length(arr)
                arr[i] + arr[j]
            end
        end
        """
    )
    @test length(StaticLint.collect_hints(cst, server)) == 4
end

@testitem "assigned but not used with loops" setup = [SLSetup] begin
    cst = parse_and_pass(
        """
        function a!(v)
            next = 0
            for i in eachindex(v)
                current = next
                next = sin(current)
                while true
                    current = next
                    next = sin(current)
                end
                v[i] = current
            end
        end
        """
    )
    @test isempty(StaticLint.collect_hints(cst, server))
    cst = parse_and_pass(
        """
        function f(v)
            next = 0
            for _ in v
                foo = next
                for _ in v
                    next = foo
                end
                foo = sin(next)
            end
        end
        """
    )
    @test isempty(StaticLint.collect_hints(cst, server))
end

@testitem "macro definition" setup = [SLSetup] begin
    cst = parse_and_pass(
        """
        module JumpToMacroDoesNotWork
            export @mymacro

            macro mymacro()
            end
        end

        JumpToMacroDoesNotWork.@mymacro(1+1)
        """
    )
    m = cst.args[end].args[1].args[2].args[1]
    methods = Set()
    for r in m.meta.ref.refs
        m = StaticLint.get_method(r)
        if m !== nothing
            push!(methods, m)
        end
    end

    @test !isempty(methods)
end

@testitem "correctly mark public bindings" setup = [SLSetup] begin
    if VERSION >= v"1.12"
        let cst = parse_and_pass(
                """
                module TopModule
                abstract type T end
                struct Foo <: T end
                export T
                public Foo

                module SubModule
                using ..TopModule
                T
                TopModule.Foo
                end

                end"""
            )
            @test refof(cst.args[1].args[3].args[3].args[1]) !== nothing
            @test refof(cst.args[1].args[3].args[4].args[1]).is_public
            @test StaticLint.refof(cst.args[1].args[3].args[5].args[3].args[3].args[2].args[1]).is_public
        end
    end
end

@testitem "IncludeLoop and DuplicateInclude" setup = [SLSetup] begin
    # Test duplicate include: main.jl includes a.jl twice
    mktempdir() do dir
        write(joinpath(dir, "a.jl"), "x = 1\n")
        write(
            joinpath(dir, "main.jl"), """
            include("a.jl")
            include("a.jl")
            """
        )
        s = StaticLint.FileServer()
        _, hints = StaticLint.lint_file(joinpath(dir, "main.jl"), s; gethints = true)
        @test any(h -> errorof(h[1]) === StaticLint.DuplicateInclude, hints)
        @test !any(h -> errorof(h[1]) === StaticLint.IncludeLoop, hints)
    end

    # Test circular include: a.jl includes b.jl, b.jl includes a.jl
    mktempdir() do dir
        write(
            joinpath(dir, "a.jl"), """
            include("b.jl")
            """
        )
        write(
            joinpath(dir, "b.jl"), """
            include("a.jl")
            """
        )
        write(
            joinpath(dir, "main.jl"), """
            include("a.jl")
            """
        )
        s = StaticLint.FileServer()
        _, hints = StaticLint.lint_file(joinpath(dir, "main.jl"), s; gethints = true)
        @test any(h -> errorof(h[1]) === StaticLint.IncludeLoop, hints)
    end
    # Test circular include: a.jl includes b.jl, b.jl includes a.jl
    mktempdir() do dir
        write(
            joinpath(dir, "a.jl"), """
            include("b.jl")
            """
        )
        write(
            joinpath(dir, "b.jl"), """
            include("./a.jl")
            """
        )
        write(
            joinpath(dir, "main.jl"), """
            include("a.jl")
            """
        )
        s = StaticLint.FileServer()
        _, hints = StaticLint.lint_file(joinpath(dir, "main.jl"), s; gethints = true)
        @test any(h -> errorof(h[1]) === StaticLint.IncludeLoop, hints)
        _, hints = StaticLint.lint_file(joinpath(dir, "a.jl"), s; gethints = true)
        @test any(h -> errorof(h[1]) === StaticLint.IncludeLoop, hints)
        _, hints = StaticLint.lint_file(joinpath(dir, "b.jl"), s; gethints = true)
        @test any(h -> errorof(h[1]) === StaticLint.IncludeLoop, hints)
    end

    # Test self-include: a.jl includes itself
    mktempdir() do dir
        write(
            joinpath(dir, "a.jl"), """
            include("a.jl")
            """
        )
        write(
            joinpath(dir, "main.jl"), """
            include("a.jl")
            """
        )
        s = StaticLint.FileServer()
        _, hints = StaticLint.lint_file(joinpath(dir, "main.jl"), s; gethints = true)
        @test any(h -> errorof(h[1]) === StaticLint.IncludeLoop, hints)
    end

    # Test no false positive: each file included exactly once
    mktempdir() do dir
        write(joinpath(dir, "a.jl"), "x = 1\n")
        write(joinpath(dir, "b.jl"), "y = 2\n")
        write(
            joinpath(dir, "main.jl"), """
            include("a.jl")
            include("b.jl")
            """
        )
        s = StaticLint.FileServer()
        _, hints = StaticLint.lint_file(joinpath(dir, "main.jl"), s; gethints = true)
        @test !any(h -> errorof(h[1]) === StaticLint.IncludeLoop, hints)
        @test !any(h -> errorof(h[1]) === StaticLint.DuplicateInclude, hints)
    end

    # Test normpath: relative paths with .. resolve correctly for includes
    mktempdir() do dir
        mkpath(joinpath(dir, "src"))
        mkpath(joinpath(dir, "src", "sub"))
        write(joinpath(dir, "src", "a.jl"), "x = 1\n")
        # include via ../src/a.jl from sub/ should resolve to the same file as src/a.jl
        write(
            joinpath(dir, "src", "sub", "b.jl"), """
            include("../a.jl")
            """
        )
        write(
            joinpath(dir, "src", "main.jl"), """
            include("a.jl")
            include("sub/b.jl")
            """
        )
        s = StaticLint.FileServer()
        _, hints = StaticLint.lint_file(joinpath(dir, "src", "main.jl"), s; gethints = true)
        @test any(h -> errorof(h[1]) === StaticLint.DuplicateInclude, hints)
        @test !any(h -> errorof(h[1]) === StaticLint.IncludeLoop, hints)
        @test !any(h -> errorof(h[1]) === StaticLint.MissingFile, hints)
    end

    # Test normpath: ./file.jl resolves the same as file.jl
    mktempdir() do dir
        write(joinpath(dir, "a.jl"), "x = 1\n")
        write(
            joinpath(dir, "main.jl"), """
            include("a.jl")
            include("./a.jl")
            """
        )
        s = StaticLint.FileServer()
        _, hints = StaticLint.lint_file(joinpath(dir, "main.jl"), s; gethints = true)
        @test any(h -> errorof(h[1]) === StaticLint.DuplicateInclude, hints)
        @test !any(h -> errorof(h[1]) === StaticLint.MissingFile, hints)
    end

    # Test normpath: circular include via .. is detected
    mktempdir() do dir
        mkpath(joinpath(dir, "sub"))
        write(
            joinpath(dir, "a.jl"), """
            include("sub/b.jl")
            """
        )
        write(
            joinpath(dir, "sub", "b.jl"), """
            include("../a.jl")
            """
        )
        write(
            joinpath(dir, "main.jl"), """
            include("a.jl")
            """
        )
        s = StaticLint.FileServer()
        _, hints = StaticLint.lint_file(joinpath(dir, "main.jl"), s; gethints = true)
        @test any(h -> errorof(h[1]) === StaticLint.IncludeLoop, hints)
    end
end

@testitem "include(joinpath(...)) with explicit strings (#311)" setup = [SLSetup] begin
    # `include(joinpath("subdir", "myfile.jl"))` should be resolved the same way
    # as `include("subdir/myfile.jl")`: the file is loaded and its bindings are
    # visible, rather than being silently ignored.
    mktempdir() do dir
        mkpath(joinpath(dir, "subdir"))
        write(joinpath(dir, "subdir", "myfile.jl"), "foo() = 1\n")
        write(
            joinpath(dir, "main.jl"), """
            include(joinpath("subdir", "myfile.jl"))
            foo()
            """
        )
        s = StaticLint.FileServer()
        _, hints = StaticLint.lint_file(joinpath(dir, "main.jl"), s; gethints = true)
        # the included file must actually be loaded
        @test StaticLint.hasfile(s, joinpath(dir, "subdir", "myfile.jl"))
        # no spurious MissingFile error
        @test !any(h -> errorof(h[1]) === StaticLint.MissingFile, hints)
        # the reference to `foo` (defined in the included file) resolves
        @test !any(h -> startswith(last(h), "Missing reference"), hints)
    end

    # Including the same file via joinpath and via a plain string must resolve to
    # the same path, which is detected as a DuplicateInclude.
    mktempdir() do dir
        mkpath(joinpath(dir, "subdir"))
        write(joinpath(dir, "subdir", "myfile.jl"), "x = 1\n")
        write(
            joinpath(dir, "main.jl"), """
            include("subdir/myfile.jl")
            include(joinpath("subdir", "myfile.jl"))
            """
        )
        s = StaticLint.FileServer()
        _, hints = StaticLint.lint_file(joinpath(dir, "main.jl"), s; gethints = true)
        @test any(h -> errorof(h[1]) === StaticLint.DuplicateInclude, hints)
    end
end

@testitem "Circular binding resolution (#404)" setup = [SLSetup] begin
    mktempdir() do dir
        write(joinpath(dir, "test2.jl"), """
        const Bar = Foo.Bar
        """)
        write(joinpath(dir, "test.jl"), """
        module Foo
        import Bar
        import Bar: foo
        include("test2.jl")
        end
        """)
        s = StaticLint.FileServer()
        x, _ = StaticLint.lint_file(joinpath(dir, "test.jl"), s; gethints=true)
        @test (StaticLint.semantic_pass(x); true)
    end
end

@testitem "assignment to outer local inside inner scope (#393)" setup = [SLSetup] begin
    has_unused(cst) = any(errorof(x) === StaticLint.UnusedBinding for (_, x) in StaticLint.collect_hints(cst, getenv(server.files[""], server)))

    # Assigning to a variable that is already a local in an enclosing scope
    # reassigns that variable rather than introducing a new (unused) local.
    # A `let` block (the case from the issue):
    @test !has_unused(parse_and_pass(
        """
        function f()
            x = 1
            let y = 2
                x = y + 1
            end
            return x
        end"""))

    # Nested `let` blocks:
    @test !has_unused(parse_and_pass(
        """
        function f()
            x = 1
            let
                let
                    x = 2
                end
            end
            return x
        end"""))

    # A closure capturing and reassigning an outer local:
    @test !has_unused(parse_and_pass(
        """
        function f()
            x = 1
            g() = (x = 2)
            g()
            return x
        end"""))

    # A `do` block (also a closure):
    @test !has_unused(parse_and_pass(
        """
        function f()
            x = 1
            map([1]) do _
                x = 2
            end
            return x
        end"""))

    # Nested soft scopes reaching an enclosing local:
    @test !has_unused(parse_and_pass(
        """
        function f()
            x = 1
            for i in 1:2
                for j in 1:2
                    x = i + j
                end
            end
            return x
        end"""))

    # A genuinely unused local introduced inside a `let` is still flagged.
    @test has_unused(parse_and_pass(
        """
        function f()
            let
                z = 1
            end
        end"""))

    # An explicit `local` inside a `let` introduces a distinct binding rather
    # than reassigning the outer variable: here the outer `x` is used while the
    # inner `local x` is not, so the inner one is still flagged.
    @test has_unused(parse_and_pass(
        """
        function f()
            x = 1
            @show x
            let
                local x = 2
            end
        end"""))
end

@testitem "closures referencing variables defined later (#313)" setup = [SLSetup] begin
    env = getenv(server.files[""], server)
    has_unused(cst) = any(errorof(x) === StaticLint.UnusedBinding for (_, x) in StaticLint.collect_hints(cst, env))
    # A missing reference is collected as an identifier hint with no associated error code.
    has_missingref(cst) = any(errorof(x) === nothing for (_, x) in StaticLint.collect_hints(cst, env))

    let cst = parse_and_pass(
        """
        function f()
            function g()
                println("hello, \$(who)")
            end
            who = "world"
            g()
        end""")
        @test !has_missingref(cst)
        @test !has_unused(cst)
    end

    let cst = parse_and_pass(
        """
        function f()
            g() = who
            who = 1
            g()
        end""")
        @test !has_missingref(cst)
        @test !has_unused(cst)
    end

    let cst = parse_and_pass(
        """
        function f()
            function g()
                function h()
                    return who
                end
                h()
            end
            who = 1
            g()
        end""")
        @test !has_missingref(cst)
        @test !has_unused(cst)
    end

    let cst = parse_and_pass(
        """
        function f()
            let
                g() = v
                v = 1
                g()
            end
        end""")
        @test !has_missingref(cst)
        @test !has_unused(cst)
    end

    let cst = parse_and_pass(
        """
        function f()
            g() = undefined_var
            g()
        end""")
        @test has_missingref(cst)
        @test !has_unused(cst)
    end

    let cst = parse_and_pass(
        """
        function foo()
            function bar()
                x = 2
            end
            local x
            bar()
            return x
        end""")
        @test !has_missingref(cst)
        @test !has_unused(cst)
        local_x = bindingof(cst[1][3][2][2])
        return_x = refof(cst[1][3][4][2])
        @test return_x === local_x
    end

    let cst = parse_and_pass(
        """
        function f()
            function g()
                return x
            end
            local x = 10
            g()
        end""")
        @test !has_missingref(cst)
        @test !has_unused(cst)
    end

    let cst = parse_and_pass(
        """
        function f()
            function g1()
                return v
            end
            function g2()
                return v + 1
            end
            v = 1
            g1() + g2()
        end""")
        @test !has_missingref(cst)
        @test !has_unused(cst)
    end

    let cst = parse_and_pass(
        """
        function foo()
            function reader()
                return x
            end
            function writer()
                x = 2
            end
            local x
            writer()
            reader()
        end""")
        @test !has_missingref(cst)
        @test !has_unused(cst)
    end

    let cst = parse_and_pass(
        """
        function f()
            function g()
                function h()
                    x = 99
                end
                h()
            end
            local x
            g()
            return x
        end""")
        @test !has_missingref(cst)
        @test !has_unused(cst)
    end

    let cst = parse_and_pass(
        """
        function foo()
            function bar()
                tmp = x + 1
                x = tmp
                return tmp
            end
            local x = 0
            bar()
            return x
        end""")
        @test !has_missingref(cst)
        @test !has_unused(cst)
    end

    let cst = parse_and_pass(
        """
        function foo()
            function bar()
                y = 2
            end
            bar()
        end""")
        @test has_unused(cst)
    end
end

@testitem "function definition satisfying a `local` declaration (#349)" setup = [SLSetup] begin
    has_error(cst, err) = any(errorof(x) === err for (_, x) in StaticLint.collect_hints(cst, getenv(server.files[""], server)))

    @test !has_error(parse_and_pass(
        """
        function fun()
            local inner_fun
            let
                inner_fun(x) = x
            end
        end"""), StaticLint.CannotDefineFuncAlreadyHasValue)

    @test !has_error(parse_and_pass(
        """
        function fun()
            local inner_fun
            inner_fun(x) = x
        end"""), StaticLint.CannotDefineFuncAlreadyHasValue)

    @test has_error(parse_and_pass(
        """
        function fun()
            local inner_fun
            inner_fun = 1
            inner_fun(x) = x
        end"""), StaticLint.CannotDefineFuncAlreadyHasValue)

    @test has_error(parse_and_pass(
        """
        function fun()
            inner_fun = 1
            inner_fun(x) = x
        end"""), StaticLint.CannotDefineFuncAlreadyHasValue)
end

@testitem "constructors on parameterized type aliases (#394)" setup = [SLSetup] begin
    has_error(cst, err) = any(errorof(x) === err for (_, x) in StaticLint.collect_hints(cst, getenv(server.files[""], server)))

    let cst = parse_and_pass(
            """
            module M
            struct Container{T}
                value::T
            end
            const IntContainer = Container{Int}
            function IntContainer(x::Float64)
                return IntContainer(round(Int, x))
            end
            end
            """
        )
        @test !has_error(cst, StaticLint.CannotDefineFuncAlreadyHasValue)
    end
    let cst = parse_and_pass(
            """
            module M
            struct Foo{A,B} end
            const Bar = Foo{Int}
            const Baz = Bar{Int}
            Baz() = 1
            end
            """
        )
        @test !has_error(cst, StaticLint.CannotDefineFuncAlreadyHasValue)
    end
    # Aliasing a `UnionAll` via a `where` clause is also a valid constructor target.
    let cst = parse_and_pass(
            """
            const MyVec = Vector{T} where T

            MyVec(x::Int64) = [x]
            """
        )
        @test !has_error(cst, StaticLint.CannotDefineFuncAlreadyHasValue)
    end
    # Multiple type variables in the `where` clause.
    let cst = parse_and_pass(
            """
            const MyArray = Array{T,N} where {T,N}

            MyArray(x::Int64) = [x]
            """
        )
        @test !has_error(cst, StaticLint.CannotDefineFuncAlreadyHasValue)
    end
    # User-defined struct aliased through a `where` clause.
    let cst = parse_and_pass(
            """
            module M
            struct Foo{T} end
            const Bar = Foo{T} where T
            Bar(x::Int64) = 1
            end
            """
        )
        @test !has_error(cst, StaticLint.CannotDefineFuncAlreadyHasValue)
    end
end

@testitem "@enum with explicit values (#275)" setup = [SLSetup] begin
    missing_refs(cst) = [x for (_, x) in StaticLint.collect_hints(cst, getenv(server.files[""], server)) if !StaticLint.haserror(x)]

    # Members given explicit values must still be bound and exportable.
    let cst = parse_and_pass("@enum Foo x=1; export x")
        @test isempty(missing_refs(cst))
    end

    let cst = parse_and_pass("@enum Foo x=1 y=2")
        @test isempty(missing_refs(cst))
    end

    # Block form with explicit values.
    let cst = parse_and_pass(
            """
            @enum Foo begin
                x = 1
                y = 2
            end
            export x, y
            """
        )
        @test isempty(missing_refs(cst))
    end

    # Mixed bare and explicit-value members.
    @test check_resolved(
        """
        @enum E a b=2 c
        E
        a
        b
        c
        """
    ) == [true, true, true, true, true, true, true, true, true]
end

@testitem "using Base in baremodule (#368)" setup = [SLSetup] begin
    missing_refs(cst) = [x for (_, x) in StaticLint.collect_hints(cst, getenv(server.files[""], server)) if !StaticLint.haserror(x)]

    # Top-level baremodule (no enclosing module to supply Base).
    let cst = parse_and_pass(
            """
            baremodule Flags
            using Base: @enum
            @enum Flag flag
            end
            """
        )
        baseid = find_first(cst, x -> StaticLint.headof(x) === :IDENTIFIER && CSTParser.valof(x) == "Base")
        @test baseid !== nothing
        @test StaticLint.hasref(baseid)
        @test isempty(missing_refs(cst))
    end
end

@testitem "hint offsets with unicode (#253)" setup = [SLSetup] begin
    # Hint offsets are byte offsets into the source. Multibyte unicode
    # characters (e.g. `α`) preceding an error must not shift the reported
    # offset off the start of the flagged expression.
    src = """
    struct Buz
        x::Integers
        α::Array{Float65,1}
    end
    """
    cst = parse_and_pass(src)
    cu = codeunits(src)
    hints = StaticLint.collect_hints(cst, getenv(server.files[""], server))

    # For every hint, the byte offset + span must extract the expression's own
    # text from the source (when the expression carries a value).
    for (offset, x) in hints
        v = CSTParser.valof(x)
        v isa String || continue
        snippet = String(cu[offset+1:offset+x.span])
        @test snippet == v
    end

    # The `Float65` typo sits after the multibyte `α`; its offset must be the
    # byte offset (after α's 2 bytes), not the character offset.
    float65 = find_first(cst, x -> StaticLint.headof(x) === :IDENTIFIER && CSTParser.valof(x) == "Float65")
    @test float65 !== nothing
    off = first(o for (o, x) in hints if x === float65)
    @test String(cu[off+1:off+float65.span]) == "Float65"
    @test off == first(findfirst("Float65", src)) - 1  # 0-based byte offset
end

@testitem "global definition inside local scope (#315)" setup = [SLSetup] begin
    let cst = parse_and_pass(
            """
            let x = 1
                global function foo()
                end
            end

            function bar()
                foo()
            end
            """
        )
        @test isempty(StaticLint.collect_hints(cst, getenv(server.files[""], server)))
    end

    let cst = parse_and_pass(
            """
            let
                global gvar = 1
                global gstruct_field = 2
                global gfunc(x) = x
                global struct GStruct end
            end

            use_gvar() = gvar
            use_gfunc() = gfunc(1)
            use_gstruct() = GStruct
            """
        )
        @test isempty(StaticLint.collect_hints(cst, getenv(server.files[""], server)))
    end

    let cst = parse_and_pass(
            """
            let
                global single
                single = 1
            end

            use_single() = single
            """
        )
        use = last(filter(id -> CSTParser.valof(id) == "single", get_ids(cst)))
        @test refof(use) !== nothing
    end

    let cst = parse_and_pass(
            """
            let
                global foo, bar, baz
                foo = 1
                bar = 2
                baz = 3
            end

            use() = foo + bar + baz
            """
        )
        uses = filter(id -> CSTParser.valof(id) in ("foo", "bar", "baz"), get_ids(cst))[end-2:end]
        @test all(id -> refof(id) !== nothing, uses)
    end
end

@testitem "issue #282 (missing reference in macrocall args)" setup = [SLSetup] begin
    let cst = parse_and_pass(
            """
            macro Jacobian(u, v, w)
                :( (u, v) -> \$w )
            end
            f = @Jacobian(u, v, u+v^2)
            """
        )
        @test isempty(StaticLint.collect_hints(cst, getenv(server.files[""], server)))
    end

    let cst = parse_and_pass(
            """
            macro m(x)
                :(\$x)
            end
            @m(undefined_var)
            """
        )
        @test isempty(StaticLint.collect_hints(cst, getenv(server.files[""], server)))
    end

    # still check identifiers in user specified local scopes in macro calls
    let cst = parse_and_pass(
            """
            \"\"\"
            docstring
            \"\"\"
            function foo()
                undefined_in_body
            end
            """
        )
        hints = StaticLint.collect_hints(cst, getenv(server.files[""], server))
        @test length(hints) == 1
        @test CSTParser.valof(hints[1][2]) == "undefined_in_body"
    end
end
