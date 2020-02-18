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
getfile(server::FileServer, path::String) = server.files[path]
getsymbolserver(server::FileServer) = server.symbolserver


function scopepass(file, target = nothing)
    server = file.server
    setscope!(getcst(file), Scope(nothing, getcst(file), Dict(), Dict{String,Any}("Base" => getsymbolserver(server)["Base"], "Core" => getsymbolserver(server)["Core"]), false))
    state = State(file, target, [getpath(file)], scopeof(getcst(file)), false, EXPR[], server)
    state(getcst(file))
    for uref in state.urefs
        s = retrieve_delayed_scope(uref)
        if s !== nothing
            resolve_ref(uref, s, state)
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

getserver(file::File) = file.server

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
    if typof(x) === Call && length(x.args) == 4
        parg = x.args[3]
        if CSTParser.is_lit_string(parg)
            path = CSTParser.str_value(parg)
            return normpath(path)
        elseif typof(parg) === x_Str && length(parg.args) == 2 && CSTParser.isidentifier(parg.args[1]) && valof(parg.args[1]) == "raw" && typof(parg.args[2]) === CSTParser.LITERAL && (kindof(parg.args[2]) == CSTParser.Tokens.STRING || kindof(parg.args[2]) == CSTParser.Tokens.TRIPLE_STRING)
            return normpath(CSTParser.str_value(parg.args[2]))
        elseif typof(parg) === Call && typof(parg.args[1]) === IDENTIFIER && CSTParser.str_value(parg.args[1]) == "joinpath"
            path_elements = String[]

            for i = 2:length(parg.args)
                arg = parg.args[i]
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

_is_macrocall_to_BaseDIR(arg) = typof(arg) === CSTParser.MacroCall && length(arg.args) == 1 &&
    typof(arg.args[1]) === CSTParser.MacroName && length(arg.args[1].args) == 2 &&
    valof(arg.args[1].args[2]) == "__DIR__"
