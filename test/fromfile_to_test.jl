module am
export MyStruct

struct MyStruct
    x::Int
end
end

module am2
export MyStruct2

struct MyStruct2
    x::Int
end
end

module am3
export MyStruct31, MyStruct32

struct MyStruct31
    x::Int
end

struct MyStruct32
    x::Int
end
end