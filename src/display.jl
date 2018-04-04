function Base.display(s::Scope, depth = 0)
    println(" "^depth, "| ", s.t.name.name, " @ ", s.index, " / ", s.offset)
    for a in s.children
        display(a, depth + 1)
    end
end

function Base.display(server::DocumentServer)
    for (file,f) in server.files
        println(basename(file), " -> ", [(basename(i.file), i.index) for i in f.state.includes])
    end
end
