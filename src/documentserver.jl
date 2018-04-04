mutable struct File
    cst::CSTParser.EXPR
    state
    scope
end
CST(f::File) = f.cst
mutable struct DocumentServer
    files::Dict{String,File}
end
DocumentServer() = DocumentServer(Dict())
getfile(server::DocumentServer, p) = server.files[p]
setfile(server::DocumentServer, p, x) = server.files[p] = x

# Base.setindex!(ds::DocumentServer, x, i) = ds.files[i] = x
# Base.getindex(ds::DocumentServer, i) = ds.files[i]


function isloaded(server::DocumentServer, path, root)
    if haskey(server.files, path)
        loaded = true
    elseif haskey(server.files, joinpath(dirname(root), path))
        path = joinpath(dirname(root), path)
        loaded = true
    elseif isabspath(path) && isfile(path)
        loadfile(server, path)
        loaded = true
    elseif isfile(joinpath(dirname(root), path))
        path = joinpath(dirname(root), path)
        loadfile(server, path)
        loaded = true
    else
        loaded = false
    end
    return loaded ? path : ""
end


function loadfile(server::DocumentServer, path, index = ())
    code = readstring(path)
    cst = CSTParser.parse(code, true)
    state = State(Location(path, 0), Dict(), Reference[], [], server)
    state.bindings["using"] = [Binding(Location("", 0), index, 0, SymbolServer.server["Base"]), Binding(Location("", 0), index, 0, SymbolServer.server["Core"])]
    state.bindings["module"] = Binding[]
    s = Scope(nothing, Scope[], cst.span, 0, CSTParser.TopLevel, index)
    scope = pass(cst, state, s, index, false, false)
    setfile(server, path, File(cst, state, scope))
end

function loaddir(dir::String, server::DocumentServer = DocumentServer())
    for (root, dirs, files) in walkdir(dir)
        for file in files
            if endswith(file, ".jl")
                path = joinpath(root, file)
                path in keys(server.files) && continue
                loadfile(server, path)
            end
        end
    end
    return server
end