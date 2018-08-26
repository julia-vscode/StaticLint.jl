CST(f::File) = f.cst
mutable struct DocumentServer
    files::Dict{String,File}
end
DocumentServer() = DocumentServer(Dict())
function Base.display(server::DocumentServer)
    for (file,f) in server.files
        println(basename(file), " -> ", [(basename(i.file), i.index) for i in f.state.includes])
    end
end

getfile(server::DocumentServer, p) = server.files[p]
setfile(server::DocumentServer, p, x) = server.files[p] = x

is_loaded(server, path) = haskey(server.files, path)

can_load(server, path) = isfile(path)

function load_file(server, path::String, index, nb, parent)
    code = read(path, String)
    cst = CSTParser.parse(code, true)
    state = State(Location(path, 0), Dict(), Reference[], [], server)
    init_bindings(state.bindings, parent)
    s = Scope(nothing, Scope[], cst.span,  CSTParser.TopLevel, index, nb, Set())
    scope = pass(cst, state, s, index, false, false)
    file = File(cst, state, scope, index, nb, parent, ResolvedRef[], Reference[])
    setfile(server, path, file)
    return file
end

function loaddir(dir::String, server::DocumentServer = DocumentServer())
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