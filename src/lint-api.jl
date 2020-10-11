export lint_string
"""
    lint_string(str::AbstractString, root = nothing, server = get_symol_server()[1])

Lint the given string and get the result as a CST.
"""
function lint_string(str::AbstractString, root = nothing, server = SymbolServer.get_symol_server()[1])
    # parse
    cst = CSTParser.parse_code(str)

    # TODO: we should not need to write to a file!

    # Write to file
    filepath = mktemp()[1]
    Base.write(filepath, str)

    # File
    file = StaticLint.File(filepath, str, cst, root, server)

    # Get bindings and scopes
    StaticLint.scopepass(file)

    return file.cst
end


"""
    isjuliafile(filepath::AbstractString)

return true if it is a julia file.
"""
function isjuliafile(filepath::AbstractString)
    ext = splitext(filepath)[2]
    return ext == ".jl"
end

export lint_file
"""
    lint_file(filepath::AbstractString, root = nothing, server = SymbolServer.get_symbol_server()[1])

Lint the given file and get the result as a StaticLint.File
"""
function lint_file(filepath::AbstractString, root = nothing, server = SymbolServer.get_symbol_server()[1])

    # Check extention
    if !isjuliafile(filepath)
        error("$filepath is not a julia file.")
    end

    # read
    str = Base.read(filepath, String)

    # parse_code
    cst = CSTParser.parse_code(str)

    # File
    file = StaticLint.File(filepath, str, cst, root, server)

    # Get bindings and scopes
    StaticLint.scopepass(file)

    return file
end


using Pkg: develop
using CodeTools: getmodule

export lint_module
"""
    lint_module(modul::Module)
    lint_module(module_name::String)

lint a module and get the result as a StaticLint.File

# Examples
```julia
using Test1
fileserver = lint_module(Test1)
```

```julia
fileserver = lint_module("./test")
```
"""
function lint_module(path::AbstractString)
    module_name, modul_path = module_name_root(path)
    Pkg.develop(path=modul_path)
    modul = CodeTools.getmodule(module_name)
    if isnothing(modul)
        module_sym = Symbol(module_name)
        @eval using $module_sym  # will throw error for Pkg if not available
        modul = CodeTools.getmodule(module_name)
    end
    return lint_module(modul)
end

# Since the module is loaded it will give the modulefiles easily
function lint_module(modul::Module, env_path = dirname(pathof(modul)))
    symbolserver, symbol_extends = SymbolServer.get_symbol_server()
    parentfile_path, included_files_path = modulefiles(modul)

    root = lint_module_file(parentfile_path, nothing, symbolserver)

    included_files_path_len = length(included_files_path)
    files = Vector{File}(undef, included_files_path_len)
    for ifile = 1:included_files_path_len
        files[i] = lint_module_file(included_files_path[i], root, symbolserver)
    end

    allfiles_path = prepend!(included_files_path, [parentfile_path])
    allfiles = prepend!(files, [root])

    files = Dict( file_path => file for (file_path, file) in zip(allfiles_path, allfiles))
    roots = Set([root])

    return FileServer(files, roots, symbolserver, symbol_extends)
end

export lint_module_file
function lint_module_file(filepath::AbstractString, root = nothing, server = nothing)

    # Check extention
    if !isjuliafile(filepath)
        error("$filepath is not a julia file.")
    end

    # read
    str = Base.read(filepath, String)

    # parse_code
    cst = CSTParser.parse_code(str)

    # File
    return StaticLint.File(filepath, str, cst, root, server)
end
