function is_joinpathable(x)
    if x isa CSTParser.EXPR{CSTParser.Call} && x.args[1] isa CSTParser.IDENTIFIER && CSTParser.str_value(x.args[1]) == "joinpath"
        joinpathable = true
        for i = 2:length(x.args)
            arg = x.args[i]
            if !(arg isa CSTParser.PUNCTUATION)
                joinpathable &= CSTParser.is_lit_string(arg)
            end
        end
        return joinpathable
    end
    return false
end

function get_path(x::CSTParser.EXPR{CSTParser.Call})
    if length(x.args) == 4
        parg = x.args[3]
        if CSTParser.is_lit_string(parg)
            path = CSTParser.str_value(parg)
            return path
        elseif parg isa CSTParser.EXPR{CSTParser.Call} && parg.args[1] isa CSTParser.IDENTIFIER && CSTParser.str_value(parg.args[1]) == "joinpath"
            path = ""
            for i = 2:length(parg.args)
                arg = parg.args[i]
                if arg isa CSTParser.PUNCTUATION
                elseif CSTParser.is_lit_string(arg)
                    path = string(path, "/", CSTParser.str_value(arg))
                else
                    return ""
                end
            end
            return path
        end
    end
    return ""
end



function follow_include(x, s, S::State{FileSystem})
    path = get_path(x)
    path = isabspath(path) ? path : joinpath(dirname(S.loc.path), path)
    !isfile(path) && return

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
