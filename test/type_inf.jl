@testset "fieldname inference" begin
# arg1 is inferred as T -> only a single (user defined) 
# datatype has the field `fieldname1`
let cst = parse_and_pass("""
    struct T
        fieldname1
    end
    function f(arg1)
        arg1.fieldname1
    end
    """)
    @test cst[2].meta.scope.names["arg1"].type === cst.meta.scope.names["T"]
end

# arg1 inferred as above
# arg2 as above but for `S`
# arg3 field use is conflicting -> no type assigned
let cst = parse_and_pass("""
    struct T
        fieldname1
    end
    struct S
        fieldname2
    end
    function f(arg1, arg2, arg3)
        arg1.fieldname1
        arg2.fieldname2
        arg3.fieldname1
        arg3.fieldname2
    end
    """)
    @test cst[3].meta.scope.names["arg1"].type === cst.meta.scope.names["T"]
    @test cst[3].meta.scope.names["arg2"].type === cst.meta.scope.names["S"]
    @test cst[3].meta.scope.names["arg3"].type === nothing
end

# arg1 type inferred as above
# arg2 type  not inferred as `sig` is also the fieldname of
# `Method` exported by Core.
let cst = parse_and_pass("""
    struct T
        fieldname1
        sig
    end
    function f(arg1, arg2)
        arg1.fieldname1
        arg2.sig
    end
    """)
    @test cst[2].meta.scope.names["arg1"].type === cst.meta.scope.names["T"]
    @test cst[2].meta.scope.names["arg2"].type === nothing
end

let cst = parse_and_pass("""
    struct T
        fieldname1
    end
    struct S
        fieldname2
    end
    function f(arg1)
        if arg1 isa T
            arg1.fieldname1
        elseif arg1 isa S
            arg1.fieldname2
        end
    end
    """)
    @test cst[3].meta.scope.names["arg1"].type === nothing
end
end

@testset "inference by use as function argument" begin
# single method function with user defined datatype
let cst = parse_and_pass("""
    struct T end
    function f(arg::T) end
    function g(arg) end
    let arg1 = unknownvalue, arg2 = unknownvalue
        f(arg1)
        g(arg1)
    end
    """)
    @test cst[4].meta.scope.names["arg1"].type === cst.meta.scope.names["T"]
    @test cst[4].meta.scope.names["arg2"].type === nothing
end

# as above against imported (symbolserver) types
let cst = parse_and_pass("""
    function f(arg::Int) end
    let arg = unknownvalue
        f(arg)
    end
    """)
    @test cst[2].meta.scope.names["arg"].type.name == SymbolServer.FakeTypeName(Int)
end

# 2 methods, conflicting types so no inference
let cst = parse_and_pass("""
    function f(arg::Int) end
    function f(arg::Float64) end
    let arg = unknownvalue
        f(arg)
    end
    """)
    @test cst[3].meta.scope.names["arg"].type === nothing
end

# 2 functions, 1 with two methods. 
let cst = parse_and_pass("""
    function f(arg::Int) end
    function f(arg::Float64) end
    function g(arg::Int) end
    let arg = unknownvalue
        f(arg)
        g(arg)
    end
    """)
    @test cst[4].meta.scope.names["arg"].type.name == SymbolServer.FakeTypeName(Int)
end

# SymServer function w/ single method 
let cst = parse_and_pass("""
    let arg = unknownvalue
        dirname(arg)
    end
    """)
    @test cst[1].meta.scope.names["arg"].type.name == SymbolServer.FakeTypeName(AbstractString)
end
# As above but qualified name for function.
let cst = parse_and_pass("""
    let arg = unknownvalue
        Base.dirname(arg)
    end
    """)
    @test cst[1].meta.scope.names["arg"].type.name == SymbolServer.FakeTypeName(AbstractString)
end
end