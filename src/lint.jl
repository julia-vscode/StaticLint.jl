mutable struct LintState
    
end

function lintpass(x::CSTParser.LeafNode, f::File, ls::LintState, loc::Location)
    loc.offset += x.fullspan
end

function lintpass(x, f::File, ls::LintState, loc::Location)
    for a in x
        lintpass(a, f, ls, loc)
    end
    
end

# Check number of args is compatible with func declarations
function check_func_nargs(x, f, ls, loc)
    if x isa CSTParser.EXPR{CSTParser.Call}
        fname = CSTParser.get_name(x)
        nargs = 0
        for i = 3:length(x.args)
            x.args[i] isa CSTParser.PUNCTUATION && continue
            if x.args[i] isa CSTParser.EXPR{CSTParser.Parameters}
                nargs += div(length(x.args[i].args) + 1, 2)
            else
                nargs += 1
            end
        end
        rref = find_ref(f, loc.offset)
        if rref isa ResolvedRef
            ms = get_methods(rref, f.state)
        end
    end
end

function find_ref(f, offset)
    for rref in f.rref
        if rref.r.loc.offset == offset
            return rref 
        elseif rref.r.loc.offset > offset
            break
        end
    end
    return nothing
end