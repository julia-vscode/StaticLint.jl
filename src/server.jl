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

# Interface spec.
# AbstractServer :-> (has/canload/load/set/get)file, getsymbolserver, getsymbolextends
# AbstractFile :-> (get/set)path, (get/set)root, (get/set)cst, semantic_pass, (get/set)server

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

function semantic_pass(file, target = nothing)
    server = file.server
    setscope!(getcst(file), Scope(nothing, getcst(file), Dict(), Dict{Symbol,Any}(:Base => getsymbolserver(server)[:Base], :Core => getsymbolserver(server)[:Core]), nothing))
    state = Toplevel(file, target, [getpath(file)], scopeof(getcst(file)), EXPR[], server)
    state(getcst(file))
    for x in state.delayed
        if hasscope(x)
            traverse(x, Delayed(scopeof(x), server))
        else
            ds = retrieve_delayed_scope(x)
            traverse(x, Delayed(ds, server))
        end
    end
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

"""
    get_path(x::EXPR)

Usually called on the argument to `include` calls, and attempts to determine
the path of the file to be included. Has limited support for `joinpath` calls.
"""
function get_path(x::EXPR, state)
    if CSTParser.iscall(x) && length(x.args) == 2
        parg = x.args[2]
        if CSTParser.isstringliteral(parg)
            path = CSTParser.str_value(parg)
            path = normpath(path)
            Base.containsnul(path) && throw(SLInvalidPath("Couldn't convert '$x' into a valid path. Got '$path'"))
            return path
        elseif CSTParser.ismacrocall(parg) && valof(parg.args[1]) == "@raw_str" && CSTParser.isstringliteral(parg.args[3])
            path = normpath(CSTParser.str_value(parg.args[3]))
            Base.containsnul(path) && throw(SLInvalidPath("Couldn't convert '$x' into a valid path. Got '$path'"))
            return path
        elseif CSTParser.iscall(parg) && isidentifier(parg.args[1]) && valofid(parg.args[1]) == "joinpath"
            path_elements = String[]

            for i = 2:length(parg.args)
                arg = parg[i]
                if _is_macrocall_to_BaseDIR(arg) # Assumes @__DIR__ points to Base macro.
                    push!(path_elements, dirname(getpath(state.file)))
                elseif CSTParser.isstringliteral(arg)
                    push!(path_elements, string(valofid(arg)))
                else
                    return ""
                end
            end
            isempty(path_elements) && return ""

            path = normpath(joinpath(path_elements...))
            Base.containsnul(path) && throw(SLInvalidPath("Couldn't convert '$x' into a valid path. Got '$path'"))
            return path
        end
    end
    return ""
end

_is_macrocall_to_BaseDIR(arg) = headof(arg) === :macrocall && length(arg.args) == 2 && valof(arg.args[1]) == "@__DIR__"
