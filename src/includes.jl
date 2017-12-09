function is_includable(path::String, S::State{FileSystem})
    !endswith(path, ".jl") && return false
    if isabspath(path) 
        return isfile(path)
    else
        return isfile(joinpath(dirname(S.loc.path), path))
    end
    return false
end

function follow_include(x::CSTParser.EXPR{CSTParser.Call}, s, S::State{FileSystem})
    if length(x.args) == 4 && CSTParser.is_lit_string(x.args[3])
        path = CSTParser.str_value(x.args[3])
        if is_includable(path, S)
            path = isabspath(path) ? path : joinpath(dirname(S.loc.path), path)
            # Build file structure
            parent = S.includes[S.loc.path]
            f = File(path, (parent, S.loc.offset + x.span), [])
            push!(parent.children, f)
            S.includes[path] = f

            x1 = CSTParser.parse(readstring(path), true)
            old_Sloc = S.loc
            S.loc = Location(path, 0)
            trav(x1, s, S)
            S.loc = old_Sloc
        end
    end
end
