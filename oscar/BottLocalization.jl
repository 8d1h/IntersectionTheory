module BottLocalization
using Nemo
import Nemo.AbstractAlgebra.Generic: combinations, det, dim, integral, rank, partitions
import Nemo.AbstractAlgebra: @declare_other, set_special, get_special
import Base: +, -, *, ^, parent

# this module does not depend on Oscar; this is only used to avoid conflict
import Oscar: dual

export det, dim, integral, rank, dual
export symmetric_power, exterior_power, chern, euler
export grassmannian, flag

# Generic stuff: should probably be put somewhere else
abstract type Sheaf end
parent(F::Sheaf) = F.parent
rank(F::Sheaf) = F.rank
abstract type Variety end
dim(X::Variety) = X.dim

# make combinations work for arrays
function combinations(I::UnitRange, k::Int) combinations(collect(I), k) end
function combinations(l::Vector{}, k::Int)
  [[l[i] for i in c] for c in combinations(length(l), k)]
end

###############################################################################
##
##  TnRep - n-dim representation of a torus, specified by its weights
##
struct TnRep
  n::Int
  w::Vector{}
  function TnRep(w::Vector{W}) where W
    # be sure to use fmpz to avoid overflow
    W == Int && return new(length(w), [ZZ(wi) for wi in w])
    new(length(w), w)
  end
end
dual(F::TnRep) = TnRep(-F.w)
+(F::TnRep, G::TnRep) = TnRep(vcat(F.w, G.w))
*(F::TnRep, G::TnRep) = TnRep([a+b for a in F.w for b in G.w])
det(F::TnRep) = TnRep([sum(F.w)])
ctop(F::TnRep) = prod(F.w)
function chern(n::Int, F::TnRep)
  sum([prod([F.w[i] for i in c], init=ZZ(1)) for c in combinations(F.n, n)], init=ZZ())
end
function _sym(k::Int, n::Int)
  k == 0 && return [Int[]]
  vcat([[push!(c, i) for c in _sym(k-1,i)] for i in 1:n]...)
end
function symmetric_power(k::Int, F::TnRep)
  TnRep([sum([F.w[i] for i in c], init=ZZ()) for c in _sym(k, F.n)])
end
function exterior_power(k::Int, F::TnRep)
  TnRep([sum([F.w[i] for i in c], init=ZZ()) for c in combinations(F.n, k)])
end

###############################################################################
##
##  TnBundle, TnVariety - varieties with a torus action and equivariant bundles
##
# A Tⁿ-variety X is represented as the set of fixed points X.points, each
# labelled using some value of type P (e.g. an array), and has a multiplicty e
# (orbifold multiplicty);
# 
# A Tⁿ-equivariant bundle on X is represented by its localization/restriction
# to each of the points in X.points, which will be of type `TnRep`.
abstract type TnVarietyT{P} <: Variety end

struct TnBundle{P, V <: TnVarietyT{P}} <: Sheaf
  parent::V
  rank::Int
  loc::Dict{P, TnRep}
  R::MPolyRing
  # loc is initialized to be empty
  function TnBundle(X::V, r::Int) where V <: TnVarietyT
    P = V.parameters[1]
    n = min(X.dim, r)
    R = PolynomialRing(QQ, ["c$i" for i in 1:n])[1]
    new{P, V}(X, r, Dict{P, TnRep}(), R)
  end
end

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
function Base.show(io::IO, F::TnBundle)
  print(io, "Tⁿ-equivariant bundle of rank ", F.rank, " on ", F.parent)
end
function Base.show(io::IO, X::TnVariety)
  name = get_special(X, :name)
  if name === nothing name = "Variety of dim $(X.dim)" end
  print(io, name * " with a Tⁿ-action")
end
euler(X::TnVariety) = sum(1//ZZ(e) for (p,e) in X.points) # special case of Bott's formula
function dual(F::TnBundle)
  X = F.parent
  ans = TnBundle(X, F.rank)
  for (p,e) in X.points
    ans.loc[p] = dual(F.loc[p])
  end
  ans
end
function +(F::TnBundle, G::TnBundle)
  X = F.parent
  ans = TnBundle(X, F.rank+G.rank)
  for (p,e) in X.points
    ans.loc[p] = F.loc[p] + G.loc[p]
  end
  ans
end
function *(F::TnBundle, G::TnBundle)
  X = F.parent
  ans = TnBundle(X, F.rank*G.rank)
  for (p,e) in X.points
    ans.loc[p] = F.loc[p] * G.loc[p]
  end
  ans
end
function det(F::TnBundle)
  X = F.parent
  ans = TnBundle(X, 1)
  for (p,e) in X.points
    ans.loc[p] = det(F.loc[p])
  end
  ans
end
function symmetric_power(k::Int, F::TnBundle)
  X = F.parent
  ans = TnBundle(X, binomial(F.rank+k-1, k))
  for (p,e) in X.points
    ans.loc[p] = symmetric_power(k, F.loc[p])
  end
  ans
end
function exterior_power(k::Int, F::TnBundle)
  X = F.parent
  ans = TnBundle(X, binomial(F.rank, k))
  for (p,e) in X.points
    ans.loc[p] = exterior_power(k, F.loc[p])
  end
  ans
end

# we want the same syntax `integral(chern(F))` as in Schubert calculus
struct TnBundleChern
  F::TnBundle
  c::MPolyElem
end
for T in [:(+), :(-), :(*)]
  @eval ($T)(a::TnBundleChern, b::TnBundleChern) = (
    @assert a.F == b.F;
    TnBundleChern(a.F, $T(a.c, b.c)))
end
^(a::TnBundleChern, n::Int) = TnBundleChern(a.F, a.c^n)
*(a::TnBundleChern, n::Number) = TnBundleChern(a.F, a.c*n)
*(n::Number, a::TnBundleChern) = TnBundleChern(a.F, a.c*n)

function chern(F::TnBundle)
  TnBundleChern(F, 1+sum(gens(F.R)))
end
function chern(k::Int, F::TnBundle)
  n = length(gens(F.R))
  TnBundleChern(F, k <= n ? gens(F.R)[k] : F.R())
end
function chern(F::TnBundle, x::RingElem)
  R = parent(x)
  @assert length(gens(R)) == length(gens(F.R))
  TnBundleChern(F, evaluate(x, gens(F.R)))
end
function Base.show(io::IO, c::TnBundleChern)
  print(io, "Chern class $(c.c) of $(c.F)")
end

# returns the homogeneous component of degree n w.r.t the weights [1,2,3,...]
# and the indices of variables that appear
function _homog_comp(n::Int, x::MPolyElem)
  r = length(gens(parent(x)))
  tally = p -> (t = repeat([0], r); for i in p t[i] += 1 end; t)
  ans, idx = parent(x)(), Int[]
  for p in partitions(n)
    p = collect(p)
    if max(p...) <= r
      t = tally(p)
      c = coeff(x, t)
      if c != 0
	setcoeff!(ans, t, c)
	union!(idx, p)
      end
    end
  end
  return ans, idx
end

function integral(c::TnBundleChern)
  F = c.F
  X = F.parent
  n = X.dim
  r = min(n, F.rank)
  top, idx = _homog_comp(n, c.c)
  top == 0 && return QQ()
  ans = 0
  for (p,e) in X.points # Bott's formula
    cherns = [i in idx ? chern(i, F.loc[p]) : ZZ() for i in 1:r]
    ans += top(cherns...) * (1 // (e * ctop(X.T.loc[p])))
  end
  ans
end

###############################################################################
##
##  Grassmannians and flag varieties
##
function grassmannian(k::Int, n::Int; weights::Symbol=:int)
  @assert k < n
  points = [p=>1 for p in combinations(n, k)]
  d = k*(n-k)
  G = TnVariety(d, points)
  S, Q, G.T = TnBundle(G, k), TnBundle(G, n-k), TnBundle(G, d)
  if weights == :poly # weights are polynomials
    R, u = PolynomialRing(QQ, ["u$i" for i in 1:n])
    for (p,e) in points
      S.loc[p] = TnRep([u[i] for i in p])
      Q.loc[p] = TnRep([u[i] for i in setdiff(1:n, p)])
    end
  else # weights are integers
    for (p,e) in points
      S.loc[p] = TnRep(p)
      Q.loc[p] = TnRep(setdiff(1:n, p))
    end
  end
  G.T = dual(S) * Q
  G.bundles = [S, Q]
  set_special(G, :name => "Grassmannian Gr($k, $n)")
  return G
end

function flag(dims::Int...; weights::Symbol=:int) flag(collect(dims), weights=weights) end
function flag(dims::Vector{Int}; weights::Symbol=:int)
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
  Fl.bundles = [TnBundle(Fl, r) for r in ranks]
  if weights == :poly # weights are polynomials
    R, u = PolynomialRing(QQ, ["u$i" for i in 1:n])
    for (p,e) in points
      for (i, F) in enumerate(Fl.bundles)
	F.loc[p] = TnRep([u[j] for j in p[i]])
      end
    end
  else # weights are integers
    for (p,e) in points
      for (i, F) in enumerate(Fl.bundles)
	F.loc[p] = TnRep(p[i])
      end
    end
  end
  Fl.T = sum(dual(Fl.bundles[i]) * sum([Fl.bundles[j] for j in i+1:l]) for i in 1:l-1)
  set_special(Fl, :name => "Flag variety Flag$(tuple(dims...))")
  return Fl
end

end # module
using .BottLocalization
