CST(f::File) = f.cst
mutable struct DocumentServer
    files::Dict{String,File}
    packages::Dict{String,Any}
end
DocumentServer() = DocumentServer(Dict(), Dict())

function Base.display(server::DocumentServer)
    for (file,f) in server.files
        println(basename(file), " -> ", [(basename(i.file), i.index) for i in f.state.includes])
    end
end

getfile(server::DocumentServer, p) = server.files[p]
setfile(server::DocumentServer, p, x) = server.files[p] = x

is_loaded(server::DocumentServer, path) = haskey(server.files, path)
is_loaded(server, path) = false

can_load(server, path) = isfile(path)

function load_file(server, path::String, index, nb, parent)
    code = read(path, String)
    cst = CSTParser.parse(code, true)
    state = State(path, server)
    s = Scope(nothing, Scope[], cst.span,  CSTParser.TopLevel, index, nb)
    scope = pass(cst, state, s, index, false, false)
    file = File(cst, state, scope, index, nb, "", [], [])
    setfile(server, path, file)
    return file
end

function load_dir(dir::String, pkgs)
    server= DocumentServer(Dict(), pkgs)
    for (root, dirs, files) in walkdir(dir)
        for file in files
            if endswith(file, ".jl")
                path = joinpath(root, file)
                path in keys(server.files) && continue
                load_file(server, path, (), 0, "")
            end
        end
    end
    return server
end