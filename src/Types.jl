# generic types
abstract type Bundle end
Base.parent(F::Bundle) = F.parent
rank(F::Bundle) = F.rank

abstract type Variety end
dim(X::Variety) = X.dim

abstract type VarietyHom end
domain(X::VarietyHom) = X.domain
codomain(X::VarietyHom) = X.codomain

Base.show(io::IO, F::Bundle) = print(io, "$(typeof(F).name.name) of rank $(F.rank) on $(F.parent)")
Base.show(io::IO, X::Variety) = print(io, "$(typeof(X).name.name) of dim $(X.dim)")
Base.show(io::IO, f::VarietyHom) = print(io, "$(typeof(f).name.name) from $(f.domain) to $(f.codomain)")

###############################################################################
#
# ChRing and ChRingElem
#
@doc Markdown.doc"""
    ChRing(R::MPolyRing, w::Vector{Int})
    ChRing(R::MPolyRing, w::Vector{Int}, I::sideal)
The type of a graded ring, possibly equipped with an ideal to represent a
quotient ring.
"""
@attributes mutable struct ChRing <: Ring
  R::MPolyRing
  w::Vector{Int}
  I::sideal
  function ChRing(R::MPolyRing, w::Vector{Int}, opts::Pair...)
    R = new(R, w)
    for o in opts set_attribute!(R, o) end
    return R
  end
  function ChRing(R::MPolyRing, w::Vector{Int}, I::sideal, opts::Pair...)
    I = std(I)
    R = new(R, w, I)
    for o in opts set_attribute!(R, o) end
    return R
  end
end

@doc Markdown.doc"""
    ChRingElem(R::ChRing, f::RingElem)
The type of an element of a `ChRing`.
"""
@attributes mutable struct ChRingElem <: RingElem
  parent::ChRing
  f::RingElem
  function ChRingElem(R::ChRing, f::RingElem)
    new(R, R.R(f))
  end
end

###############################################################################
#
# CobordRing and CobordRingElem
#
@attributes mutable struct CobordRing <: Ring
  base::Ring
  n::Int
  R::ChRing
  function CobordRing(; base::Ring=QQ)
    new(base, 0)
  end
end

mutable struct CobordRingElem <: RingElem
  parent::CobordRing
  n::Int
  f::ChRingElem
end

# THE cobordism ring
const Omega = CobordRing()
@doc Markdown.doc"""
    cobordism_ring()
Return $\Omega$, the (complex) cobordism ring with rational coefficients."""
function cobordism_ring(; base::Ring = QQ)
  base == QQ && return Omega
  cache = get_attribute(Omega, :base)
  if cache == nothing
    cache = Dict{Ring, CobordRing}()
    set_attribute!(Omega, :base => cache)
  end
  if !(base in keys(cache))
    O = CobordRing(base = base)
    cache[base] = O
  end
  cache[base]
end

function Base.show(io::IO, R::ChRing)
  print(io, "ChRing generated by ", tuple(gens(R.R)...), " of degree ", tuple(R.w...))
  if isdefined(R, :I)
    print(io, ", with relations ", tuple(Singular.gens(R.I)...))
  end
  if base_ring(R) isa Singular.N_FField
    print(io, ", with parameters ", tuple(Singular.transcendence_basis(base_ring(R))...))
  end
end

# allow reduction
(R::ChRing)(f::RingElement; reduce::Bool=false) = begin
  if !(parent(f) == R.R) f = R.R(f) end
  if reduce && isdefined(R, :I) f = Singular.reduce(f, R.I) end
  ChRingElem(R, f)
end
(R::ChRing)() = R(0)
zero(R::ChRing) = R(0)
one(R::ChRing) = R(1)
gens(R::ChRing) = R.(gens(R.R))
base_ring(R::ChRing) = base_ring(R.R)

(R::ChRing)(x::ChRingElem) = R(x.f)
zero(x::ChRingElem) = zero(parent(x))
one(x::ChRingElem) = one(parent(x))
mul!(c::ChRingElem, a::ChRingElem, b::ChRingElem) = (c.f = (a*b).f; c)
add!(c::ChRingElem, a::ChRingElem, b::ChRingElem) = (add!(c.f, a.f, b.f); c)
addeq!(a::ChRingElem, b::ChRingElem) = (addeq!(a.f, b.f); a)

copy(x::ChRingElem) = parent(x)(x.f)
# avoid changing the parent ring
deepcopy(x::ChRingElem) = parent(x)(deepcopy(x.f))

@doc Markdown.doc"""
    ChAlgHom(A::ChRing, B::ChRing, image::Vector)
The type of a ring homomorphism between two `ChRing`s.
"""
mutable struct ChAlgHom
  domain::ChRing
  codomain::ChRing
  image::Vector{ChRingElem}
  salg::Singular.SAlgHom
  function ChAlgHom(A::ChRing, B::ChRing, image::Vector{ChRingElem})
    salg = Singular.AlgebraHomomorphism(A.R, B.R, [x.f for x in image])
    new(A, B, image, salg)
  end
  function ChAlgHom(A::ChRing, B::ChRing, image::Vector)
    image = B.(image)
    ChAlgHom(A, B, image)
  end
end

function (f::ChAlgHom)(x::ChRingElem)
  @assert x.parent == f.domain
  f.codomain(f.salg(x.f), reduce=true)
end

function *(f::ChAlgHom, g::ChAlgHom)
  A, B = f.domain, f.codomain
  @assert B == g.domain
  C = g.codomain
  ChAlgHom(A, C, g.(f.image))
end

function expressify(x::ChRingElem; context = nothing)
  ans = Expr(:call, :+)
  d = total_degree(x)
  comps = [c.f for c in x[0:d] if !iszero(c)]
  for c in comps # print by homogeneous terms
    push!(ans.args, expressify(c, context = context))
  end
  return ans
end

Nemo.elem_type(::Type{ChRing}) = ChRingElem

# for now _coerce does nothing
function _coerce(x::ChRingElem, y::ChRingElem)
  A, B = x.parent, y.parent
  A == B && return x, y
  X = get_attribute(A, :variety)
  Y = get_attribute(B, :variety)
  try
    return x, pullback(_hom(X, Y), y)
  catch
    try
      return pullback(_hom(Y, X), x), y
    catch
      error("the sheaves are not on compatible varieties")
    end
  end
end

Base.parent(x::ChRingElem) = x.parent
Nemo.parent_type(::Type{ChRingElem}) = ChRing

# promotion
for T in [:Int, :Rational, :fmpz, :fmpq, :n_Q, :n_transExt]
  @eval promote_rule(::Type{ChRingElem}, ::Type{$T}) = ChRingElem
end
promote_rule(::Type{ChRingElem}, ::Type{<:Singular.n_unknown}) = ChRingElem
promote_rule(::Type{ChRingElem}, ::Type{<:MPolyElem}) = ChRingElem
promote_rule(::Type{ChRingElem}, ::Type{CobordRingElem})= ChRingElem

# arithmetic
-(x::ChRingElem) = x.parent(-x.f)
# reduction for `*` and `^` only
for (O, reduce) in [:(+) => false, :(-) => false, :(*) => true]
  @eval function $O(x::ChRingElem, y::ChRingElem)
    x, y = _coerce(x, y)
    x.parent($O(x.f, y.f), reduce=$reduce)
  end
end
function ^(x::ChRingElem, n::Int)
  n < 0 && return inv(x^-n)
  Base.power_by_squaring(x, n)
end
function ==(x::ChRingElem, y::ChRingElem)
  x, y = _coerce(x, y)
  simplify(x).f == simplify(y).f
end

coeff(x::ChRingElem, exps::Vector{Int}) = coeff(x.f, exps)
Nemo.terms(x::ChRingElem) = parent(x).(Nemo.terms(x.f))

function total_degree(x::ChRingElem)
  R = x.parent
  f = R(x.f, reduce=true).f
  f == 0 && return -1
  max([sum(parent(x).w .* Singular.degrees(t)) for t in Singular.terms(f)]...)
end

function ishomogeneous(x::ChRingElem)
  R = x.parent
  f = R(x.f, reduce=true).f
  f == 0 && return true
  degs = [sum(parent(x).w .* Singular.degrees(t)) for t in Singular.terms(f)]
  all(d -> d==degs[1], degs)
end

function div(x::ChRingElem, y::ChRingElem)
  x, y = _coerce(x, y)
  x.parent(div(simplify(x).f, simplify(y).f))
end
function Nemo.divexact(x::ChRingElem, y::ChRingElem)
  x, y = _coerce(x, y)
  x.parent(Nemo.divexact(simplify(x).f, simplify(y).f))
end
Nemo.isunit(x::ChRingElem) = Nemo.isunit(simplify(x)[0].f)

function Base.getindex(x::ChRingElem, n::Int)
  R = x.parent
  d = get_attribute(R, :truncate)
  d !== nothing && n > d && return R(0)
  f = R(x.f, reduce=true).f
  ans = R(0)
  for t in Singular.terms(f)
    if sum(R.w .* Singular.degrees(t)) == n
      ans += t end
  end
  ans
end

function Base.getindex(x::ChRingElem, I::UnitRange)
  R = x.parent
  f = R(x.f, reduce=true).f
  ans = repeat([R(0)], length(I))
  d = get_attribute(R, :truncate)
  stop = (d === nothing) ? I.stop : min(I.stop, d)
  for t in Singular.terms(f)
    d = R.w' * Singular.degrees(t)
    if d ≥ I.start && d ≤ stop
      ans[d - I.start + 1] += t end
  end
  ans
end

function simplify(x::ChRingElem)
  R = x.parent
  n = get_attribute(R, :truncate)
  # no dimension restriction
  n === nothing && return R(x.f, reduce=true)
  # otherwise keep only terms in degree ≤ n
  n < 0 && return R()
  return sum(x[0:n])
end

simplify!(x::ChRingElem) = (x.f = simplify(x).f; x)

# add all the relations to a Chow ring due to dimension
function trim!(R::ChRing)
  d = get_attribute(R, :truncate)
  if isdefined(R, :I)
    gI = gens(R.I)
    # check that I is homogeneous, using the weights of R
    @assert all(g -> ishomogeneous(R(g)), gI)
  else
    gI = Singular.spoly[]
  end
  if !isdefined(R, :I) || Singular.dimension(R.I) > 0 
    # add powers of variables so that the ideal becomes 0-dimensional
    # below we will use kbase to further trim all the terms of degree > dim
    for (i,x) in enumerate(gens(R.R))
      push!(gI, x^Int(ceil((d+1)//R.w[i])))
    end
  end
  b = gens(Singular.kbase(std(Ideal(R.R, gI...))))
  R.I = std(Ideal(R.R, vcat(gI, filter(x -> total_degree(R(x)) > d, b))...))
  return R
end

function add_vars(R::ChRing, vars::Vector{Pair{Int, String}}; w::Vector{Int}=Int[], prod_ordering=false)
  base = base_ring(R.R)
  syms = vcat([_parse_symbol(s, 1:k) for (k,s) in vars]..., string.(gens(R.R)))
  n = sum(k for (k,_) in vars)
  if length(w) == 0 w = repeat([1], n) end
  @assert length(w) == n
  ord = prod_ordering ? ordering_dp(n) * R.R.ord : :degrevlex
  Rx, x = polynomial_ring(base, syms, ordering=ord)
  toRx = Singular.AlgebraHomomorphism(R.R, Rx, x[n+1:end])
  isdefined(R, :I) && return ChRing(Rx, vcat(w, R.w), Ideal(Rx, toRx.(gens(R.I))))
  return ChRing(Rx, vcat(w, R.w))
end

function add_rels!(R::ChRing, rels::Vector{Singular.spoly{T}}) where T
  @assert all(g -> parent(g) == R.R, rels)
  R.I = isdefined(R, :I) ? std(R.I + Ideal(R.R, rels)) : std(Ideal(R.R, rels))
  return R
end

function graded_ring(R::Singular.PolyRing{T}, w::Vector{Int}, rels::Vector{Singular.spoly{T}}) where T
  ChRing(R, w, Ideal(R, rels))
end
graded_ring(F::Ring, symb::Vector{String}, opts::Pair...) = graded_ring(F, symb, repeat([1], length(symb)), opts...)
function graded_ring(F::Ring, symb::Vector{String}, w::Vector{Int}, opts::Pair...)
  R = Nemo.PolynomialRing(F, symb)[1]
  S = ChRing(R, w)
  for o in opts set_attribute!(S, o) end
  S, gens(S)
end

# copied from Oscar. I should really start migrating to Oscar...
abstract type GAPGroup <: AbstractAlgebra.Group end
abstract type GAPGroupElem{T<:GAPGroup} <: AbstractAlgebra.GroupElem end
struct BasicGAPGroupElem{T<:GAPGroup} <: GAPGroupElem{T}
  parent::T
  X::GapObj
end
Base.show(io::IO, x::GAPGroupElem) =  print(io, GAP.gap_to_julia(GAP.Globals.StringViewObj(x.X)))
Base.show(io::IO, x::GAPGroup) = print(io, GAP.gap_to_julia(GAP.Globals.StringViewObj(x.X)))
*(x::BasicGAPGroupElem, y::BasicGAPGroupElem) = (@assert x.parent == y.parent; BasicGAPGroupElem(x.parent, x.X * y.X))

function cyc(cycles::AbstractVector{T}...) where T <: Union{Base.Integer, fmpz}
  if cycles == Tuple([])
    cycles = [Int[]]
  end
  prod([GG.CycleFromList(GAP.julia_to_gap(Int.(c))) for c in cycles])
end

@attributes mutable struct WeylGroup <: GAPGroup
  X::GapObj
  gens::Vector{GapObj} # generators
  p::GapObj # the presentation
  typ::Char
  function WeylGroup(str::String, I=nothing; implementation::Symbol=:perm)
    typ, n = str[1], parse(Int, str[2:end])
    # For type A, the permutation representation is meaningful: (i,i+1) is the
    # transposition of coordinates.
    # For type B,C,D, the permutation representation is simply faster than the
    # matrix representation, e.g., when using `StructureDescription`
    if typ in ['A', 'B', 'C', 'D'] && implementation == :perm
      if typ == 'A'
	gs = [cyc([i, i+1]) for i in 1:n]
      elseif typ == 'B' || typ == 'C'
	gs = push!([cyc([i, i+1], [n+i, n+i+1]) for i in 1:n-1], cyc([n, 2n]))
      elseif typ == 'D'
	gs = push!([cyc([i, i+1], [n+i, n+i+1]) for i in 1:n-2], cyc([n-1, n], [2n-1, 2n]), cyc([2n-1, n], [n-1, 2n]))
      end
    elseif typ in ['E', 'F', 'G'] || implementation == :matrix
      L = GG.SimpleLieAlgebra(GAP.julia_to_gap(string(typ)), n, GG.Rationals)
      gs = GG.GeneratorsOfGroup(GG.WeylGroup(GG.RootSystem(L)))
      gs = GAP.gap_to_julia(Vector{GapObj}, gs)
    else
      error("not implemented")
    end
    if I != nothing
      gs = [gs[i] for i in intersect(1:n, I)]
    end
    G = GG.Group(gs...)
    # WI = GG.Subgroup(G, GAP.julia_to_gap(GapObj[gs[i] for i in intersect(1:n, I)]))
    p = GG.EpimorphismFromFreeGroup(G)
    W = new(G, gs, p, typ)
    if typ == 'A'
      action = (w, f) -> (
	for i in _factor(w)
	  f = Singular.permute_variables(f, [j==i ? i+1 : j==i+1 ? i : j for j in 1:n+1], parent(f))
	end; f)
    elseif typ == 'B' || typ == 'C'
      action = (w, f) -> (
	for i in _factor(w)
	  if i < n
	    f = Singular.permute_variables(f, [j==i ? i+1 : j==i+1 ? i : j for j in 1:n], parent(f))
	  else
	    x = gens(parent(f))
	    f = f(x[1:end-1]..., -x[end])
	  end
	end; f)
    elseif typ == 'D'
      action = (w, f) -> (
	for i in _factor(w)
	  if i < n
	    f = Singular.permute_variables(f, [j==i ? i+1 : j==i+1 ? i : j for j in 1:n], parent(f))
	  else
	    x = gens(parent(f))
	    f = f(x[1:end-2]..., -x[end], -x[end-1])
	  end
	end; f)
    else
      action = nothing
    #   error("not implemented")
    end
    set_attribute!(W, :action => action)
    return W
  end
end
function weyl_group(str::String, I=nothing; implementation::Symbol=:perm) WeylGroup(str, I, implementation=implementation) end

const WeylGroupElem = BasicGAPGroupElem{WeylGroup}

# XXX add check
(W::WeylGroup)(x::GapObj) = WeylGroupElem(W, x)
(W::WeylGroup)(cycs::AbstractVector{T}...) where T <: Union{Int, fmpz} = W(cyc(cycs...))
(W::WeylGroup)(p::AbstractAlgebra.Generic.Perm{T}) where T <: Union{Int, fmpz} = W(cyc([c for c in Nemo.cycles(p)]...))
# (W::WeylGroup)(x::PermGroupElem) = WeylGroupElem(W, x.X)
