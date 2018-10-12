f = """
var1 = 1
var1
""" |> test_sl

@test isempty(f.uref)
@test f.rref[1].b.val == f.cst.args[1].arg2

# ext_binding 
f = """
module M end
baremodule BM end
function f1 end
function f2() end
abstract type at end
primitive type pt 8 end
struct s end
mutable struct ms end
""" |> test_sl

@test isempty(f.uref)
@test length(f.state.bindings[()]) == 8

# macro
f = """
macro m() end
""" |> test_sl

@test_broken isempty(f.uref)

# assignemnt 
f = """
a = 1
(b,c,d) = 1,1,1
f() = 1
""" |> test_sl

@test isempty(f.uref)
@test length(f.state.bindings[()]) == 5

# parameters
f = """
abstract type AT1 end
abstract type AT2{T} end
""" |> test_sl

@test isempty(f.uref)
@test length(f.state.bindings[()]) == 2
@test length(f.state.bindings[(4,)]) == 1

# typealias
f = """
TA{T} = Int{T}
""" |> test_sl

@test_broken isempty(f.uref)
@test length(f.state.bindings[()]) == 1


# try block
f = """
try 
    1 + 1
catch
end
""" |> test_sl

@test isempty(f.uref)

f = """
try 
    1 + 1
catch e
    e
end
""" |> test_sl

@test isempty(f.uref)


f = """
abstract type T end
-a = a
-(a) = a
-(a::T) = a
-a::T = a
~a = a
a + b = a + b
+(a,b) = a + b
+(a::T,b::T) = a + b
""" |> test_sl
@test isempty(f.uref)