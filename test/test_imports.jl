# imports
f = """
module A
a = 1
export a
end
using .A
A.a
""" |> test_sl

@test isempty(f.uref)

f = """
module A
a = 1
export a
end
using .A
a
""" |> test_sl

@test_broken isempty(f.uref)