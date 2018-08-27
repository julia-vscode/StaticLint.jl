include("../src/symbolserver.jl")
if !isdir("../store")
    mkdir("../store")
end
SymbolServer.save(SymbolServer.build_base_store(), "../store/base.jstore")
SymbolServer.save_pkg_store("../store")