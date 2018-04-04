module SymbolServer
const initted = false
import StaticLint:Binding,Location

mutable struct ModuleBinding
    exported::Set{Symbol}
    internal::Set{Symbol}
    loaded::Dict{String,Binding}
    is_loaded::Bool
    load_failed::Bool
end

function load_module(m::String)
    if m in keys(server)
        if server[m].is_loaded
            return true
        elseif server[m].load_failed
            return false
        else
            try
                eval(:(import $(Symbol(m))))
                M = getfield(Main, Symbol(m))
                load_module(M)
                server[m].is_loaded = true
            catch
                server[m].load_failed = true
            end
            return server[m].is_loaded
        end
    else
        return false
    end
end

function load_module(m::Module, load = false, force = false) 
    mname = string(first(methods(getfield(m, :eval))).module)
    if haskey(server, mname) && (server[mname].is_loaded && !force)
        return
    end
    
    server[mname] = ModuleBinding(Set(names(m)), Set(names(m, true, true)), Dict(), true, false)
    for i in server[mname].internal
        !isdefined(m, i) && continue
        x = getfield(m, i)
        if x isa Module
            load_module(x)
        end
        server[mname].loaded[String(i)] = Binding(Location("", 0), (), -1, x)
    end
end

function load_binding(m::String, b::String)
    if haskey(server, m)

    end
end

const pkgdir = Pkg.dir()
pkgdir = "c:/Users/zacnu/.julia/v0.6"
const installed_packages = filter(p->isdir(joinpath(pkgdir,p)) && p!="METADATA" && !startswith(p,"."), readdir(pkgdir))
const server = Dict{String,ModuleBinding}()

function init()
    initted && return
    load_module(Main.Base)
    load_module(Main.Core)
    for pkg in installed_packages
        if isfile(joinpath(pkgdir, pkg, "src", join([pkg, ".jl"])))
            server[pkg] = ModuleBinding(Set{String}(), Set{String}(), Dict(), false, false)
        end
    end
    global initted = true
end

end
