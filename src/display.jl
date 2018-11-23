Base.display(si::SIndex) = print(si.i, ":", si.n)
Base.display(r::Reference) = (print(Expr(r.val), " @ [", splitdir(r.loc.file)[2], ",", ); display(r.si); print("]"))
Base.display(rr::ResolvedRef) = (display(rr.r);print(" -> ");display(rr.b))
Base.display(b::Binding) = (print("Binding{", splitdir(b.loc.file)[2]); display(b.si); print("}"))
Base.display(b::ImportBinding) = (print("ImportBinding{", splitdir(b.loc.file)[2]); display(b.si); print("}"))
function Base.display(X::Array{T}) where T <: Union{Reference,Binding,ImportBinding,ResolvedRef} 
    n = length(X)
    print(n, "-element Array{$T}\n ")
    if n < 25
        for x in X
            display(x)
            print("\n ")
        end
    else
        for i in 1:12
            display(X[i])
            print("\n ")
        end
        print("    .\n ")
        print("    .\n ")
        for i in n-12:n
            display(X[i])
            print("\n ")
        end
    end
end


function Base.display(state::State)
    println("[State ($(state.loc.file)) w/ ")
    println("      $(length(state.bindings)) bindings") 
    println("      $(length(state.modules.list)) modules")     
    println("      $(length(state.refs)) references]")   
end

function Base.display(s::Scope, depth = 0)
    println(" "^depth, "| ", s.t.name.name, " @ ", s.index, " / ", s.offset)
    for a in s.children
        display(a, depth + 1)
    end
end

Base.display(f::File) = println("File (", f.parent, " -> [", join([splitdir(inc.file)[2] for inc in f.state.includes], ","), "]) with ", length(f.cst.args), " args.")