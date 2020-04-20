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
    symbol_extends::Dict{SymbolServer.VarRef, Vector{SymbolServer.VarRef}}
    symbol_fieldtypemap::Dict{Symbol, Vector{SymbolServer.VarRef}}
end
FileServer() = FileServer(Dict{String,File}(), Set{File}(), deepcopy(SymbolServer.stdlibs), SymbolServer.collect_extended_methods(SymbolServer.stdlibs), fieldname_type_map(SymbolServer.stdlibs))

# Interface spec.
# AbstractServer :-> (has/canload/load/set/get)file, getsymbolserver, getsymbolextends
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
getsymbolextendeds(server::FileServer) = server.symbol_extends
getsymbolfieldtypemap(server::FileServer) = server.symbol_fieldtypemap

function scopepass(file, target = nothing)
    server = file.server
    setscope!(getcst(file), Scope(nothing, getcst(file), Dict(), Dict{Symbol,Any}(:Base => getsymbolserver(server)[:Base], :Core => getsymbolserver(server)[:Core]), false))
    state = State(file, target, [getpath(file)], scopeof(getcst(file)), false, EXPR[], server)
    state(getcst(file))
    for uref in state.urefs
        s = retrieve_delayed_scope(uref)
        if s !== nothing
            resolve_ref(uref, s, state, [])
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
    if typof(x) === Call && length(x) == 4
        parg = x[3]
        if CSTParser.is_lit_string(parg)
            path = CSTParser.str_value(parg)
            return normpath(path)
        elseif typof(parg) === x_Str && length(parg) == 2 && CSTParser.isidentifier(parg[1]) && valof(parg[1]) == "raw" && typof(parg[2]) === CSTParser.LITERAL && (kindof(parg[2]) == CSTParser.Tokens.STRING || kindof(parg[2]) == CSTParser.Tokens.TRIPLE_STRING)
            return normpath(CSTParser.str_value(parg[2]))
        elseif typof(parg) === Call && typof(parg[1]) === IDENTIFIER && CSTParser.str_value(parg[1]) == "joinpath"
            path_elements = String[]

            for i = 2:length(parg)
                arg = parg[i]
                if typof(arg) === PUNCTUATION
                elseif _is_macrocall_to_BaseDIR(arg) # Assumes @__DIR__ points to Base macro.
                    push!(path_elements, dirname(getpath(state.file)))
                elseif CSTParser.is_lit_string(arg)
                    push!(path_elements, string(CSTParser.str_value(arg)))
                else
                    return ""
                end
            end
            path = normpath(joinpath(path_elements...))
            return path
        end
    end
    return ""
end

_is_macrocall_to_BaseDIR(arg) = typof(arg) === CSTParser.MacroCall && length(arg) == 1 &&
    typof(arg[1]) === CSTParser.MacroName && length(arg[1]) == 2 &&
    valof(arg[1][2]) == "__DIR__"
