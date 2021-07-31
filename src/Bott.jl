###############################################################################
#
# TnRep - n-dim representation of a torus, specified by its weights
#
@doc Markdown.doc"""
    TnRep(w::Vector)

The type of a representation of a torus, specified by its weights.
"""
struct TnRep
  n::Int
  w::Vector
  function TnRep(w::Vector{W}) where W
    # be sure to use fmpz to avoid overflow
    W <: Integer && return new(length(w), ZZ.(w))
    new(length(w), w)
  end
end
dual(F::TnRep) = TnRep(-F.w)
+(F::TnRep, G::TnRep) = TnRep(vcat(F.w, G.w))
*(F::TnRep, G::TnRep) = TnRep([a+b for a in F.w for b in G.w])
det(F::TnRep) = TnRep([sum(F.w)])
ctop(F::TnRep) = prod(F.w)
# chern(k::Int, F::TnRep) = sum(prod.(combinations(F.w, k)))
# perform the enumeration manually: this can save some unnecessary allocation
chern(k::Int, F::TnRep) = _chern_dfs!(F.w, F.n, k)
function _chern_dfs!(v::Vector, n::Int, k::Int)
  k < 1 && return one(v[1])
  ans = zero(v[1])
  for m in n:-1:k
    ans += v[m] * _chern_dfs!(v, m - 1, k - 1)
  end
  return ans
end

###############################################################################
#
# TnBundle, TnVariety - varieties with a torus action and equivariant bundles
#
# A Tⁿ-variety X is represented as the set of fixed points X.points, each
# labelled using some value of type P (e.g. an array), and has a multiplicty e
# (orbifold multiplicty);
# 
# A Tⁿ-equivariant bundle on X is represented by its localization/restriction
# to each of the points in X.points, which will be of type `TnRep`.
# They are stored as a function to allow lazy evaluation: this is crucial for
# large examples, since otherwise we may run into memory problems.
abstract type TnVarietyT{P} <: Variety end

@doc Markdown.doc"""
    TnBundle(X::TnVariety, r::Int, f::Function)

The type of a torus-equivariant bundle, represented by its localizations to the
fixed points of the base variety.
"""
mutable struct TnBundle{P, V <: TnVarietyT{P}} <: Bundle
  parent::V
  rank::Int
  loc::Function
  @declare_other
  function TnBundle(X::V, r::Int) where V <: TnVarietyT
    P = V.parameters[1]
    new{P, V}(X, r)
  end
  function TnBundle(X::V, r::Int, f::Function) where V <: TnVarietyT
    P = V.parameters[1]
    new{P, V}(X, r, f)
  end
end

@doc Markdown.doc"""
    TnVariety(n::Int, points)

The type of a variety with a torus action, represented by the fixed points.
"""
mutable struct TnVariety{P} <: TnVarietyT{P}
  dim::Int
  points::Vector{Pair{P, Int}}
  T::TnBundle
  bundles::Vector{TnBundle}
  @declare_other
  function TnVariety(n::Int, points::Vector{Pair{P, Int}}) where P
    new{P}(n, points)
  end
end

euler(X::TnVariety) = sum(1//ZZ(e) for (p,e) in X.points) # special case of Bott's formula
tangent_bundle(X::TnVariety) = X.T
cotangent_bundle(X::TnVariety) = dual(X.T)
bundles(X::TnVariety) = X.bundles
OO(X::TnVariety) = TnBundle(X, 1, p -> TnRep([0]))

function *(X::TnVariety, Y::TnVariety)
  points = [[p[1],q[1]] => p[2]*q[2] for (p, q) in Base.Iterators.product(X.points, Y.points)][:]
  XY = TnVariety(dim(X) + dim(Y), points)
  T = TnBundle(XY, dim(XY), p -> TnRep(vcat(X.T.loc(p[1]).w, Y.T.loc(p[2]).w)))
  XY.T = T
  return XY
end

dual(F::TnBundle) = TnBundle(F.parent, F.rank, p -> dual(F.loc(p)))
+(F::TnBundle, G::TnBundle) = TnBundle(F.parent, F.rank + G.rank, p -> F.loc(p) + G.loc(p))
*(F::TnBundle, G::TnBundle) = TnBundle(F.parent, F.rank * G.rank, p -> F.loc(p) * G.loc(p))
det(F::TnBundle) = TnBundle(F.parent, 1, p -> det(F.loc(p)))

function symmetric_power(k::Int, F::TnBundle)
  TnBundle(F.parent, binomial(F.rank+k-1, k), p -> (
    TnRep(sum.(_sym(F.loc(p).w, k)))))
end
function exterior_power(k::Int, F::TnBundle)
  TnBundle(F.parent, binomial(F.rank, k), p -> (
    TnRep(sum.(combinations(F.loc(p).w, k)))))
end

# we want the same syntax `integral(chern(F))` as in Schubert calculus
# the following ad hoc type represents a formal expression in chern classes of a bundle F
struct TnBundleChern
  F::TnBundle
  c::ChRingElem
end
for O in [:(+), :(-), :(*)]
  @eval $O(a::TnBundleChern, b::TnBundleChern) = (
    @assert a.F == b.F;
    TnBundleChern(a.F, $O(a.c, b.c)))
end
^(a::TnBundleChern, n::Int) = TnBundleChern(a.F, a.c^n)
*(a::TnBundleChern, n::RingElement) = TnBundleChern(a.F, a.c*n)
*(n::RingElement, a::TnBundleChern) = TnBundleChern(a.F, n*a.c)
Base.sqrt(a::TnBundleChern) = TnBundleChern(a.F, sqrt(a.c))
Base.show(io::IO, c::TnBundleChern) = print(io, "Chern class $(c.c) of $(c.F)")

# create a ring to hold the chern classes of F
function _get_ring(F::TnBundle)
  if get_special(F, :R) === nothing
    r = min(F.parent.dim, F.rank)
    R = graded_ring(QQ, _parse_symbol("c", 1:r), collect(1:r), :truncate => F.parent.dim)[1]
    set_special(F, :R => R)
  end
  get_special(F, :R)
end

chern(F::TnBundle) = TnBundleChern(F, 1+sum(gens(_get_ring(F))))
chern(X::TnVariety) = chern(X.T)
chern(k::Int, F::TnBundle) = TnBundleChern(F, chern(F).c[k])
chern(k::Int, X::TnVariety) = chern(k, X.T)
ctop(F::TnBundle) = chern(F.rank, F)
chern(F::TnBundle, x::MPolyElem) = begin
  R = _get_ring(F)
  @assert length(gens(R)) == length(gens(parent(x)))
  TnBundleChern(F, Nemo.evaluate(x, gens(R)))
end
ch(F::TnBundle) = chern(F, F.rank + _logg(chern(F).c).f)
chi(p::Int, X::TnVariety) = integral(chern(X.T, chi(p, variety(dim(X))).f))
todd(X::TnVariety) = chern(X.T, todd(dim(X)).f)
signature(X::TnVariety) = integral(chern(X.T, signature(variety(dim(X))).f))
a_hat_genus(X::TnVariety) = integral(chern(X.T, a_hat_genus(variety(dim(X))).f))

# compute multiple integrals simultaneously to avoid redundant computations
# used in `chern_numbers` for example
function _integral(cc::Vector{TnBundleChern})
  F, R = cc[1].F, parent(cc[1].c)
  @assert all(c -> c.F == F, cc)
  X = F.parent
  n, r = X.dim, length(gens(R))
  top = [c.c[n].f for c in cc]
  exp_vec = sum(vcat(sum.(Nemo.exponent_vectors.(top))))
  idx = filter(i -> exp_vec[i] > 0, 1:r)
  top = [[(a, _exp_to_partition(v)) for (a,v) in zip(Nemo.coefficients(t), Nemo.exponent_vectors(t))] for t in top]
  ans = Vector{Any}[repeat([0], Threads.nthreads()) for _ in cc]
  Threads.@threads for (p,e) in X.points # Bott's formula
    Fp = F.loc(p)
    cherns = [i in idx ? chern(i, Fp) : 0 for i in 1:r]
    cT = ctop(X.T.loc(p))
    for i in 1:length(cc)
      if cT isa AbstractFloat
	t = sum(typeof(cT)(convert(Rational{BigInt}, a)) * prod(cherns[k] for k in v) for (a,v) in top[i])
	ans[i][Threads.threadid()] += t * 1 / (e * cT)
      else
	t = sum(a * prod(cherns[k] for k in v) for (a,v) in top[i])
	ans[i][Threads.threadid()] += t * 1 // (e * cT)
      end
    end
  end
  _round.(sum.(ans))
end

_round(x::AbstractFloat) = (n = round(x); @assert abs(n - x) < 1e-3; QQ(BigInt(n)))
_round(x::fmpq) = x
_round(x::AbstractAlgebra.Generic.Frac) = QQ(numerator(x)) // QQ(denominator(x))

function integral(c::TnBundleChern)
  _integral([c])[1]
end

function chern_number(X::TnVariety, λ::AbstractVector{Int})
  sum(λ) == dim(X) || error("not a partition of the dimension")
  c = [chern(i, X) for i in 1:dim(X)]
  integral(prod([c[i] for i in λ]))
end

function chern_numbers(X::TnVariety, P::Vector{T}=partitions(dim(X)); nonzero::Bool=false) where T <: Partition
  all(λ -> sum(λ) == dim(X), P) || error("not a partition of the dimension")
  c = [chern(i, X) for i in 1:dim(X)]
  ans = _integral([prod([c[i] for i in λ]) for λ in P])
  Dict([λ => ci for (ci, λ) in zip(ans, P) if !nonzero || ci != 0])
end

###############################################################################
#
# Grassmannians and flag varieties
#
# utility function that parses the weight specification
function _parse_weight(n::Int, w)
  w == :int   && return ZZ.(1:n)
  w == :poly  && return Nemo.PolynomialRing(QQ, ["u$i" for i in 1:n])[2]
  w == :float && return Float128.(1:n)
  if (w isa UnitRange) w = collect(w) end
  w isa Vector && length(w) == n && return w
  error("incorrect specification for weights")
end

function tn_grassmannian(k::Int, n::Int; weights=:int)
  @assert k < n
  points = [p=>1 for p in combinations(n, k)]
  d = k*(n-k)
  G = TnVariety(d, points)
  w = _parse_weight(n, weights)
  S = TnBundle(G, k, p -> TnRep([w[i] for i in p]))
  Q = TnBundle(G, n-k, p -> TnRep([w[i] for i in setdiff(1:n, p)]))
  G.bundles = [S, Q]
  G.T = dual(S) * Q
  set_special(G, :description => "Grassmannian Gr($k, $n)")
  return G
end

function tn_flag(dims::Vector{Int}; weights=:int)
  n, l = dims[end], length(dims)
  ranks = pushfirst!([dims[i+1]-dims[i] for i in 1:l-1], dims[1])
  @assert all(r->r>0, ranks)
  d = sum(ranks[i] * sum(dims[end]-dims[i]) for i in 1:l-1)
  function enum(i::Int, rest::Vector{Int})
    i == l && return [[rest]]
    [pushfirst!(y, x) for x in combinations(rest, ranks[i]) for y in enum(i+1, setdiff(rest, x))]
  end
  points = [p=>1 for p in enum(1, collect(1:n))]
  Fl = TnVariety(d, points)
  w = _parse_weight(n, weights)
  Fl.bundles = [TnBundle(Fl, r, p -> TnRep([w[j] for j in p[i]])) for (i, r) in enumerate(ranks)]
  Fl.T = sum(dual(Fl.bundles[i]) * sum([Fl.bundles[j] for j in i+1:l]) for i in 1:l-1)
  set_special(Fl, :description => "Flag variety Flag$(tuple(dims...))")
  return Fl
end

@doc Markdown.doc"""
    linear_subspaces_on_hypersurface(k::Int, d::Int)

Compute the number of $k$-dimensional subspaces on a generic degree-$d$
hypersurface in a projective space of dimension $n=\frac1{k+1}\binom{d+k}d+k$.

The computation uses Bott's formula by default. Use the argument `bott=false`
to switch to Schubert calculus.
"""
function linear_subspaces_on_hypersurface(k::Int, d::Int; bott::Bool=true)
  n = Int(binomial(d+k, d) // (k+1)) + k
  G = grassmannian(k+1, n+1, bott=bott)
  S, Q = G.bundles
  integral(ctop(symmetric_power(d, dual(S))))
end

function _hilb(n::Int, parts::Vector, w::Vector)
  points = [p=>1 for p in vcat([collect(Base.Iterators.product(partitions.(pp)...))[:] for pp in parts]...)]
  H = TnVariety(2n, points)
  loc(p) = begin
    ws = typeof(w[1][2])[]
    for (k,(λ,μ)) in enumerate(w)
      if length(p[k]) > 0
	b = conj(p[k])
	for (s,j) in enumerate(p[k])
	  for i in 1:j
	    push!(ws, λ*(i-j-1) + μ*(b[i]-s))
	    push!(ws, λ*(j-i)   + μ*(s-b[i]-1))
	  end
	end
      end
    end
    TnRep(ws)
  end
  H.T = TnBundle(H, 2n, loc)
  return H
end

# Ellingsrud-Strømme
# On the homology of the Hilbert scheme of points in the plane
@doc Markdown.doc"""
    hilb_P2(n::Int)
Construct the Hilbert scheme of $n$ points on $\mathbf P^2$ as a `TnVariety`.
"""
function hilb_P2(n::Int; weights=:int)
  parts = [[a-1, b-a-1, n+2-b] for (a,b) in combinations(n+2, 2)]
  if weights == :int weights = [0,1,2+n] end
  if weights == :float weights = Float128[0,1,2+n] end
  w = _parse_weight(3, weights)
  w = [(w[2]-w[1],w[3]-w[1]), (w[3]-w[2],w[1]-w[2]), (w[1]-w[3],w[2]-w[3])]
  _hilb(n, parts, w)
end

@doc Markdown.doc"""
    hilb_P1xP1(n::Int)
Construct the Hilbert scheme of $n$ points on $\mathbf P^1\times\mathbf P^1$ as
a `TnVariety`.
"""
function hilb_P1xP1(n::Int; weights=:int)
  parts = [[a-1, b-a-1, c-b-1, n+3-c] for (a,b,c) in combinations(n+3, 3)]
  if weights == :int weights = [0,1,2,3+n] end
  if weights == :float weights = Float128[0,1,2,3+n] end
  w = _parse_weight(4, weights)
  w = [(w[1]-w[4],w[2]-w[3]), (w[4]-w[1],w[2]-w[3]), (w[1]-w[4],w[3]-w[2]), (w[4]-w[1],w[3]-w[2])]
  _hilb(n, parts, w)
end
