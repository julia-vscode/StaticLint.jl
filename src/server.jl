#=
Project trees are usually made up of multiple files. An AbstractServer holds the AbstractFiles that represent this tree. FileServer is the basic implementation and assumes files are available and readable from disc. (LanguageServer illustrates another implementaiton). The accompanying functions summarised below are required for making an alternative implementation. 

Interface spec.
AbstractServer :-> (has/canload/load/set/get)file, getsymbolserver, getsymbolextends
AbstractFile :-> (get/set)path, (get/set)root, (get/set)cst, semantic_pass, (get/set)server
=#
abstract type AbstractServer end
abstract type AbstractFile end

mutable struct File
    path::String
    source::String
    cst::EXPR
    root::Union{Nothing,File}
    server
end

mutable struct FileServer <: AbstractServer
    files::Dict{String,File}
    roots::Set{File}
    symbolserver::SymbolServer.EnvStore
    symbol_extends::Dict{SymbolServer.VarRef,Vector{SymbolServer.VarRef}}
end
FileServer() = FileServer(Dict{String,File}(), Set{File}(), deepcopy(SymbolServer.stdlibs), SymbolServer.collect_extended_methods(SymbolServer.stdlibs))

hasfile(server::FileServer, path::String) = haskey(server.files, path)
canloadfile(server, path) = isfile(path)
function setfile(server::FileServer, path::String, file::File)
    server.files[path] = file
end
getfile(server::FileServer, path::String) = server.files[path]
function loadfile(server::FileServer, path::String)
    source = read(path, String)
    cst = CSTParser.parse(source, true)
    f = File(path, source, cst, nothing, server)
    setroot(f, f)
    setfile(server, path, f)
    return getfile(server, path)
end
getsymbolserver(server::FileServer) = server.symbolserver
getsymbolextendeds(server::FileServer) = server.symbol_extends
getsymbolserver(state::State) = getsymbolserver(state.env)
getsymbolextendeds(state::State) = getsymbolextendeds(state.env)
getsymbolserver(env::ExternalEnv) = env.symbols
getsymbolextendeds(env::ExternalEnv) = env.extended_methods


"""
    get_env(file::File, server::FileServer)

Get the relevant `ExternalEnv` for a given file. 
"""
function get_env(file::File, server::FileServer)
    # For FileServer this approach is equivalent to the previous behaviour. Other AbstractServers 
    # (e.g. LanguageServerInstance) can use this function to associate different files (or trees of 
    # files) with different environments.
    ExternalEnv(server.symbolserver, server.symbol_extends, Symbol[])
end


getpath(file::File) = file.path

getroot(file::File) = file.root
function setroot(file::File, root::File)
    file.root = root
    return file
end

getcst(file::File) = file.cst
function setcst(file::File, cst::EXPR)
    file.cst = cst
    return file
end

getserver(file::File) = file.server
function setserver(file::File, server::FileServer)
    file.server = server
    return file
end

function Base.display(f::File)
    println(f.path)
end

function Base.display(s::FileServer)
    n = length(s.files)
    println(n, "-file Server")
    cnt = 0
    for (p, f) in s.files
        cnt += 1
        println(" ", p)
        cnt > 10 && break
    end
end
