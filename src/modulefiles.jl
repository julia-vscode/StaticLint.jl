# code licensed under MIT from https://github.com/JunoLab/Atom.jl/blob/b42ce6519e96b59fd3c7172a6599dcc50a051c90/src/modules.jl#L26

export modulefiles

using Base: PkgId, UUID

"""
    parentfile, included_files = modulefiles(mod::Module)
Return the `parentfile` in which `mod` was defined, as well as a list of any
other files that were `include`d to define `mod`. If this operation is unsuccessful,
`(nothing, nothing)` is returned.
All files are returned as absolute paths.
"""
function modulefiles(mod::Module)
  # NOTE: src_file_key stuff was removed when adapted
  parentfile = String(first(methods(getfield(mod, :eval))).file)
  id = Base.PkgId(mod)
  if id.name == "Base" || Symbol(id.name) ∈ stdlib_names
    parentfile = normpath(Base.find_source_file(parentfile))
    filedata = Base._included_files
  else
    use_compiled_modules() || return nothing, nothing   # FIXME: support non-precompiled packages
    _, filedata = pkg_fileinfo(id)
  end
  filedata === nothing && return nothing, nothing
  included_files = filter(mf -> mf[1] == mod, filedata)
  return fixpath(parentfile), String[fixpath(mf[2]) for mf in included_files]
end

# Fix paths to files that define Julia (base and stdlibs)
function fixpath(
    filename::AbstractString;
    badpath = basebuilddir,
    goodpath = basepath("..")
  )
  startswith(filename, badpath) || return fullpath(normpath(filename)) # NOTE: `fullpath` added when adapted
  filec = filename
  relfilename = relpath(filename, badpath)
  relfilename0 = relfilename
  for strippath in (joinpath("usr", "share", "julia"),)
    if startswith(relfilename, strippath)
      relfilename = relpath(relfilename, strippath)
      if occursin("stdlib", relfilename0) && !occursin("stdlib", relfilename)
        relfilename = joinpath("stdlib", relfilename)
      end
    end
  end
  ffilename = normpath(joinpath(goodpath, relfilename))
  if (isfile(filename) & !isfile(ffilename))
    ffilename = normpath(filename)
  end
  fullpath(ffilename) # NOTE: `fullpath` added when adapted
end

"""
    basebuilddir
Julia's top-level directory when Julia was built, as recorded by the entries in
`Base._included_files`.
"""
const basebuilddir = let # NOTE: changed from `begin` to `let` when adapted
  sysimg = filter(x -> endswith(x[2], "sysimg.jl"), Base._included_files)[1][2]
  dirname(dirname(sysimg))
end

use_compiled_modules() = Base.JLOptions().use_compiled_modules != 0

# For tracking Julia's own stdlibs
const stdlib_names = Set([
  :Base64,
  :CRC32c,
  :Dates,
  :DelimitedFiles,
  :Distributed,
  :FileWatching,
  :Future,
  :InteractiveUtils,
  :Libdl,
  :LibGit2,
  :LinearAlgebra,
  :Logging,
  :Markdown,
  :Mmap,
  :OldPkg,
  :Pkg,
  :Printf,
  :Profile,
  :Random,
  :REPL,
  :Serialization,
  :SHA,
  :SharedArrays,
  :Sockets,
  :SparseArrays,
  :Statistics,
  :SuiteSparse,
  :Test,
  :Unicode,
  :UUIDs,
])
@static VERSION ≥ v"1.6.0-DEV.734" && push!(stdlib_names, :TOML)

function pkg_fileinfo(id::PkgId)
  uuid, name = id.uuid, id.name
  # Try to find the matching cache file
  paths = Base.find_all_in_cache_path(id)
  sourcepath = Base.locate_package(id)
  if length(paths) > 1
    fpaths = filter(path->Base.stale_cachefile(sourcepath, path) !== true, paths)
    if isempty(fpaths)
      # Work-around for #371 (broken dependency prevents tracking):
      # find the most recent cache file. Presumably this is the one built
      # to load the package.
      sort!(paths; by=path->mtime(path), rev=true)
      deleteat!(paths, 2:length(paths))
    else
      paths = fpaths
    end
  end
  isempty(paths) && return nothing, nothing
  @assert length(paths) == 1
  path = first(paths)
  provides, includes_requires = try
    parse_cache_header(path)
  catch
    return nothing, nothing
  end
  mods_files_mtimes, _ = includes_requires
  for (pkgid, buildid) in provides
    if pkgid.uuid === uuid && pkgid.name == name
      return path, mods_files_mtimes
    end
  end
end

# A near-copy of the same method in `base/loading.jl`. However, this retains the full module path to the file.
function parse_cache_header(f::IO)
  modules = Vector{Pair{PkgId,UInt64}}()
  while true
    n = read(f, Int32)
    n == 0 && break
    sym = String(read(f, n)) # module name
    uuid = UUID((read(f, UInt64), read(f, UInt64))) # pkg UUID
    build_id = read(f, UInt64) # build UUID (mostly just a timestamp)
    push!(modules, PkgId(uuid, sym) => build_id)
  end
  totbytes = read(f, Int64) # total bytes for file dependencies
  # read the list of requirements
  # and split the list into include and requires statements
  includes = Tuple{Module,String,Float64}[]
  requires = Pair{Module,PkgId}[]
  while true
    n2 = read(f, Int32)
    n2 == 0 && break
    depname = String(read(f, n2))
    mtime = read(f, Float64)
    n1 = read(f, Int32)
    mod = (n1 == 0) ? Main : Base.root_module(modules[n1].first)
    if n1 != 0
      # determine the complete module path
      while true
        n1 = read(f, Int32)
        totbytes -= 4
        n1 == 0 && break
        submodname = String(read(f, n1))
        mod = getfield(mod, Symbol(submodname))
        totbytes -= n1
      end
    end
    if depname[1] != '\0'
      push!(includes, (mod, depname, mtime))
    end
    totbytes -= 4 + 4 + n2 + 8
  end
  @assert totbytes == 12 "header of cache file appears to be corrupt"
  return modules, (includes, requires)
end

function parse_cache_header(cachefile::String)
  io = open(cachefile, "r")
  try
    !Base.isvalid_cache_header(io) && throw(ArgumentError("Invalid header in cache file $cachefile."))
    return parse_cache_header(io)
  finally
    close(io)
  end
end
