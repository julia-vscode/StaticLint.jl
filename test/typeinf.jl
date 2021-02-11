@testset "type inference by use" begin  
cst = parse_and_pass("""
struct T 
end

struct S 
end

f(x::T) = 1
g(x::S) = 1

function ex1(x)
    f(x)
end

function ex2(x)
    f(x)
    g(x)
end

function ex3(x)
    if 1
        f(x)
    else
        f(x)
    end
end

function ex4(x)
    x
    if 1
        f(x)
    end
end

function ex5(x)
    if 1
        f(x)
    else
        g(x)
    end
end

function ex6(x)
    if 1
        y = x
        f(y)
    else
        g(x)
    end
end
""");

T = cst.meta.scope.names["T"]
S = cst.meta.scope.names["S"]

@test cst.meta.scope.names["ex1"].val.meta.scope.names["x"].type == T
@test cst.meta.scope.names["ex2"].val.meta.scope.names["x"].type === nothing
@test cst.meta.scope.names["ex3"].val.meta.scope.names["x"].type === nothing
@test cst.meta.scope.names["ex4"].val.meta.scope.names["x"].type === nothing
@test cst.meta.scope.names["ex5"].val.meta.scope.names["x"].type === nothing
@test cst.meta.scope.names["ex6"].val.meta.scope.names["y"].type === T
end

