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

const Scalar = Union{Number, fmpz, fmpq, n_Q, n_transExt}

@doc Markdown.doc"""
    ChRing(R::MPolyRing, w::Vector{Int})
    ChRing(R::MPolyRing, w::Vector{Int}, I::sideal)
The type of a graded ring, possibly equipped with an ideal to represent a
quotient ring.
"""
mutable struct ChRing <: Ring
  R::MPolyRing
  w::Vector{Int}
  I::sideal
  @declare_other
  function ChRing(R::MPolyRing, w::Vector{Int}, opts::Pair...)
    R = new(R, w)
    for o in opts set_special(R, o) end
    return R
  end
  function ChRing(R::MPolyRing, w::Vector{Int}, I::sideal, opts::Pair...)
    I = std(I)
    R = new(R, w, I)
    for o in opts set_special(R, o) end
    return R
  end
end

# allow reduction
(R::ChRing)(f::Union{Scalar, RingElem}; reduce::Bool=false) = begin
  if !(parent(f) == R.R) f = R.R(f) end
  if reduce && isdefined(R, :I) f = Singular.reduce(f, R.I) end
  ChRingElem(R, f)
end
(R::ChRing)() = R(0)
zero(R::ChRing) = R(0)
one(R::ChRing) = R(1)
gens(R::ChRing) = R.(gens(R.R))

@doc Markdown.doc"""
    ChRingElem(R::ChRing, f::RingElem)
The type of an element of a `ChRing`.
"""
mutable struct ChRingElem <: RingElem
  parent::ChRing
  f::RingElem
  @declare_other
  function ChRingElem(R::ChRing, f::RingElem)
    new(R, R.R(f))
  end
end

one(::Type{ChRingElem}) = 1

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

# TODO print by homogeneous terms
Base.show(io::IO, x::ChRingElem) = show(io, x.f)
Base.show(io::IO, mi::MIME"text/latex", x::ChRingElem) = show(io, mi, x.f)
Base.show(io::IO, mi::MIME"text/html", x::ChRingElem) = show(io, mi, x.f)

Nemo.elem_type(::Type{ChRing}) = ChRingElem

# for now _coerce does nothing
function _coerce(x::ChRingElem, y::ChRingElem)
  @assert x.parent == y.parent
  x, y
end

Base.parent(x::ChRingElem) = x.parent
Nemo.parent_type(::Type{ChRingElem}) = ChRing

-(x::ChRingElem) = x.parent(-x.f)
# reduction for `*` and `^` only
for (O, reduce) in [:(+) => false, :(-) => false, :(*) => true]
  @eval $O(x::ChRingElem, y::ChRingElem) = (
    (x, y) = _coerce(x, y);
    x.parent($O(x.f, y.f), reduce=$reduce))
  for T in [:Int, :Rational, :fmpz, :fmpq, :n_Q, :n_transExt, :RingElem]
    @eval $O(a::$T, x::ChRingElem) = (
      x.parent($O(a, x.f), reduce=$reduce))
    @eval $O(x::ChRingElem, a::$T) = (
      x.parent($O(x.f, a), reduce=$reduce))
  end
end
^(x::ChRingElem, n::Int) = x.parent(x.f^n, reduce=true)

for T in [:Int, :Rational, :fmpz, :fmpq, :n_Q, :n_transExt, :RingElem]
  @eval ==(a::$T, x::ChRingElem) = x.parent(a) == x
  @eval ==(x::ChRingElem, a::$T) = x.parent(a) == x
end
==(x::ChRingElem, y::ChRingElem) = (
  (x, y) = _coerce(x, y);
  R = x.parent;
  R(x.f, reduce=true).f == R(y.f, reduce=true).f)

function total_degree(x::ChRingElem)
  R = x.parent
  f = R(x.f, reduce=true).f
  f == 0 && return 0
  max([R.w' * Singular.degrees(t) for t in Singular.terms(f)]...)
end

function ishomogeneous(x::ChRingElem)
  R = x.parent
  f = R(x.f, reduce=true).f
  f == 0 && return true
  degs = [R.w' * Singular.degrees(t) for t in Singular.terms(f)]
  all(d -> d==degs[1], degs)
end

div(x::ChRingElem, y::ChRingElem) = (
  (x, y) = _coerce(x, y);
  R = x.parent;
  xf = R(x.f, reduce=true).f;
  yf = R(y.f, reduce=true).f;
  if yf == 0 throw(DivideError) end;
  R(div(xf, yf)))

function Base.getindex(x::ChRingElem, n::Int)
  R = x.parent
  d = get_special(R, :variety_dim)
  d !== nothing && n > d && return R(0)
  f = R(x.f, reduce=true).f
  ans = R(0)
  for t in Singular.terms(f)
    if R.w' * Singular.degrees(t) == n
      ans += t end
  end
  ans
end

function Base.getindex(x::ChRingElem, I::UnitRange)
  R = x.parent
  f = R(x.f, reduce=true).f
  ans = repeat([R(0)], length(I))
  d = get_special(R, :variety_dim)
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
  n = get_special(R, :variety_dim)
  # no dimension restriction
  n === nothing && return R(x.f, reduce=true)
  # otherwise keep only terms in degree ≤ n
  n < 0 && return R.R()
  return sum(x[0:n])
end

simplify!(x::ChRingElem) = (x.f = simplify(x).f; x)

# add all the relations to a Chow ring due to dimension
function trim!(R::ChRing)
  d = get_special(R, :variety_dim)
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
  Rx, x = PolynomialRing(base, syms, ordering=ord)
  toRx = Singular.AlgebraHomomorphism(R.R, Rx, x[n+1:end])
  isdefined(R, :I) && return ChRing(Rx, vcat(w, R.w), Ideal(Rx, toRx.(gens(R.I))))
  return ChRing(Rx, vcat(w, R.w))
end

function add_rels!(R::ChRing, rels::Vector{Singular.spoly{T}}) where T
  @assert all(g -> parent(g) == R.R, rels)
  R.I = isdefined(R, :I) ? std(R.I + Ideal(R.R, rels)) : std(Ideal(R.R, rels))
  return R
end
