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
