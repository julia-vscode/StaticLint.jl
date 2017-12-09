function import_has_dots(x)
    i = 2
    while CSTParser.is_dot(x.args[i])
        i +=1
    end
    return i - 2
end

function unwrap_imports(x)
    !all(CSTParser.is_colon(a) || a isa CSTParser.PUNCTUATION || a isa CSTParser.IDENTIFIER || a isa CSTParser.KEYWORD for a in x) && return []
    prefix = Symbol[]
    vars = Vector{Symbol}[]

    i = 2
    if any(CSTParser.is_colon(a) for a in x)
        while !CSTParser.is_colon(x.args[i])
            !(x.args[i] isa CSTParser.PUNCTUATION) && push!(prefix, Symbol(x.args[i].val))
            i += 1
        end
        i += 1
    end
    
    while i <= length(x.args)
        if CSTParser.is_comma(x.args[i]) 
            i += 1
        end
        var = copy(prefix)
        while i<= length(x.args) && !CSTParser.is_comma(x.args[i])
            !(x.args[i] isa CSTParser.PUNCTUATION) && push!(var, Symbol(x.args[i].val))
            i += 1
        end
        push!(vars, var)
    end
    return vars
end

function is_pkg_available(pkg::Symbol, S::State{FileSystem})
    Pkg.installed(string(pkg)) != nothing
end

function is_pkg_loaded(pkg::Symbol, S::State{FileSystem})
    isdefined(Main, pkg)
end


function load_pkg(pkg::Symbol, S::State{FileSystem})
    if is_pkg_available(pkg, S)
        eval(:(import $(pkg)))
    end
end

function get_imports(x, S) end
function get_imports(x::CSTParser.EXPR{T}, S) where T <: Union{CSTParser.Using,CSTParser.Import,CSTParser.ImportAll}
    vars = unwrap_imports(x)
    for v in vars
        if length(v) == 1
            if is_pkg_loaded(v[1], S) && getfield(Main, v[1]) isa Module
                for n in names(getfield(Main, v[1]))
                    add_binding(string(n), :Any, S::State, S.loc.offset + x.span)
                end
            elseif is_pkg_available(v[1], S)
                load_pkg(v[1], S)
            end
        elseif length(v) == 2
            if is_pkg_loaded(v[1], S) && getfield(Main, v[1]) isa Module
                add_binding(string(v[1]), :Module, S::State, S.loc.offset + x.span)
                if v[2] in names(getfield(Main, v[1]), true, true)
                    add_binding(string(v[2]), :Any, S::State, S.loc.offset + x.span)
                end
            elseif is_pkg_available(v[1], S)
                load_pkg(v[1], S)
            end
        end
    end
end


function mod_names(m::Module, d = Dict{String,Tuple{Set{Symbol},Set{Symbol}}}())
    ext = names(m)
    int = names(m, true, true)
    d[string(m)] = (Set(ext), Set(int))
    for n in int
        if isdefined(m, n) && getfield(m, n) isa Module && !(string(getfield(m, n)) in keys(d))
            mod_names(getfield(m, n), d)
        end
    end
    d
end
