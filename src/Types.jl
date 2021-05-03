# generic types
abstract type Sheaf end
Base.parent(F::Sheaf) = F.parent
rank(F::Sheaf) = F.rank

abstract type Variety end
dim(X::Variety) = X.dim

abstract type VarietyHom end
domain(X::VarietyHom) = X.domain
codomain(X::VarietyHom) = X.codomain

Base.show(io::IO, F::Sheaf) = print(io, "$(typeof(F).name.name) of rank $(F.rank) on $(F.parent)")
Base.show(io::IO, X::Variety) = print(io, "$(typeof(X).name.name) of dim $(X.dim)")
Base.show(io::IO, f::VarietyHom) = print(io, "$(typeof(f).name.name) from $(f.domain) to $(f.codomain)")

const Scalar = Union{Number, fmpz, fmpq, n_Q, n_transExt}

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

(R::ChRing)(f::Union{Scalar, RingElem}) = ChRingElem(R, R.R(f))
(R::ChRing)() = R(0)
zero(R::ChRing) = R(0)
one(R::ChRing) = R(1)
gens(R::ChRing) = R.(gens(R.R))

mutable struct ChRingElem <: RingElem
  parent::ChRing
  f::RingElem
  @declare_other
  function ChRingElem(R::ChRing, f::RingElem)
    new(R, R.R(f))
  end
end

one(::Type{ChRingElem}) = 1
# (R::ChRing)(f::ChRingElem) = R(f.f)
# mul!(a::ChRingElem, b::ChRingElem, c::ChRingElem) = b * c
# addeq!(a::ChRingElem, b::ChRingElem) = a + b

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
  simplify(f.codomain(f.salg(x.f)))
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

-(x::ChRingElem) = ChRingElem(x.parent, -x.f)
for O in [:(+), :(-), :(*)]
  @eval ($O)(x::ChRingElem, y::ChRingElem) = (
    (x, y) = _coerce(x, y);
    ChRingElem(x.parent, $O(x.f, y.f)))
  for T in [:Int, :Rational, :fmpz, :fmpq, :n_Q, :n_transExt, :RingElem]
    @eval ($O)(a::$T, x::ChRingElem) = (
      ChRingElem(x.parent, $O(a, x.f)))
    @eval ($O)(x::ChRingElem, a::$T) = (
      ChRingElem(x.parent, $O(x.f, a)))
  end
end
^(x::ChRingElem, n::Int) = ChRingElem(x.parent, x.f^n)

for T in [:Int, :Rational, :fmpz, :fmpq, :n_Q, :n_transExt, :RingElem]
  @eval ==(a::$T, x::ChRingElem) = x.parent(a) == x
  @eval ==(x::ChRingElem, a::$T) = x.parent(a) == x
end
==(x::ChRingElem, y::ChRingElem) = (
  (x, y) = _coerce(x, y);
  @assert x.parent == y.parent;
  x = simplify(x); y = simplify(y);
  x.f == y.f)

function total_degree(x::ChRingElem)
  R, f = x.parent, x.f
  if isdefined(R, :I)
    f = Singular.reduce(f, R.I) end
  f == 0 && return 0
  max([R.w' * Singular.degrees(t) for t in Singular.terms(f)]...)
end

div(x::ChRingElem, y::ChRingElem) = (
  (x, y) = _coerce(x, y);
  x = simplify(x); y = simplify(y);
  if y == 0 throw(DivideError) end;
  ChRingElem(x.parent, div(x.f, y.f)))

Base.getindex(x::ChRingElem, n::Int) =  _homog_comp(n, x)
Base.getindex(x::ChRingElem, I::UnitRange) =  _homog_comps(I, x)

function _homog_comp(n::Int, x::ChRingElem)
  R, f = x.parent, x.f
  d = get_special(R, :variety_dim)
  d !== nothing && n > d && return R(0)
  if isdefined(R, :I)
    f = Singular.reduce(f, R.I) end
  ans = R(0)
  for t in Singular.terms(f)
    if R.w' * Singular.degrees(t) == n
      ans += t end
  end
  ans
end

function _homog_comps(I::UnitRange, x::ChRingElem)
  R, f = x.parent, x.f
  if isdefined(R, :I)
    f = Singular.reduce(f, R.I) end
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
  n === nothing && return isdefined(R, :I) ? R(Singular.reduce(x.f, R.I)) : x
  # otherwise keep only terms in degree ≤ n
  return sum(_homog_comps(0:n, x))
end

