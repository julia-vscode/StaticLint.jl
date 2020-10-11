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
