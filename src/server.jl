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
    symbolserver::Dict{String,SymbolServer.ModuleStore}
end

# Interface spec.
# AbstractServer :-> (has/canload/load/set/get)file, getsymbolserver
# AbstractFile :-> (get/set)path, (get/set)root, (get/set)cst, scopepass, (get/set)server

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


function scopepass(file)
    server = file.server
    setscope!(getcst(file), Scope(nothing, Dict(), Dict{String,Any}("Base" => getsymbolserver(server)["Base"], "Core" => getsymbolserver(server)["Core"]), false))
    state = State(file, scopeof(getcst(file)), false, false, false, EXPR[], server)
    state(getcst(file))
    for uref in state.urefs
        s = retrieve_delayed_scope(uref)
        if s !== nothing
            resolve_ref(uref, s, state)
        end
    end
end

getpath(file::File) = file.path
function setpath(file::File, path)
    file.path = path
    return file
end

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
    for (p,f) in s.files
        cnt+=1
        println(" ", p)
        cnt > 10 && break
    end
end

function get_path(x::EXPR)
    if typof(x) === Call && length(x.args) == 4
        parg = x.args[3]
        if CSTParser.is_lit_string(parg)
            path = CSTParser.str_value(parg)
            return normpath(path)
        elseif typof(parg) === Call && typof(parg.args[1]) === IDENTIFIER && CSTParser.str_value(parg.args[1]) == "joinpath"
            path = ""
            for i = 2:length(parg.args)
                arg = parg.args[i]
                if typof(arg) === PUNCTUATION
                elseif CSTParser.is_lit_string(arg)
                    path = string(path, "/", CSTParser.str_value(arg))
                else
                    return ""
                end
            end
            return normpath(path)
        end
    end
    return ""
end
