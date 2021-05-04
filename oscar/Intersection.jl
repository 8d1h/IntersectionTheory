module Intersection
using Oscar
import Base: +, -, *, /
import Oscar: AlgHom, MPolyQuo, MPolyQuoElem, Ring, Ring_dec, RingElem_dec
import Oscar: det
import Nemo.AbstractAlgebra: @declare_other, set_special, get_special

include("BottLocalization.jl")
import .BottLocalization: Sheaf, Variety
import .BottLocalization: symmetric_power, exterior_power, chern, euler

export abstract_variety, abstract_sheaf
export pullback, pushforward, betti, intersection_matrix, dual_basis
export ch, chern, ctop, euler, OO, segre, todd, pontryagin, l_genus, a_hat_genus
export chern_number, chern_numbers
export tangent_bundle, cotangent_bundle, canonical_bundle, canonical_class
export symmetric_power, exterior_power, schur_functor
export section_zero_locus, complete_intersection, degeneracy_locus
export proj, grassmannian, flag, point
export schubert_class, schubert_classes
export →
# export blowup

###############################################################################
##
##  AbstractSheaf
##
abstract type AbstractVarietyT <: Variety end

mutable struct AbstractSheaf{V <: AbstractVarietyT} <: Sheaf
  parent::V
  rank::Union{Int, RingElem}
  ch::RingElem_dec
  chern::RingElem_dec
  # from Chern character
  function AbstractSheaf(X::V, ch::RingElem_dec) where V <: AbstractVarietyT
    r = constant_coefficient(_lift(ch))
    try r = Int(ZZ(r))
    catch # r can contain symbolic variables like `n`
    end
    # ch = sum(_homog_comps(0:X.dim, ch)) # XXX truncate ch: this is very slow
    new{V}(X, r, ch)
  end
  # from rank + Chern classes: the Chern character is computed
  function AbstractSheaf(X::V, r::Int, c::RingElem_dec) where V <: AbstractVarietyT
    new{V}(X, r, r + _logg(c), c)
  end
end

function abstract_sheaf(X::V, ch::RingElem_dec) where V <: AbstractVarietyT
  AbstractSheaf(X, ch)
end

function abstract_sheaf(X::V, r::Int, c::RingElem_dec) where V <: AbstractVarietyT
  AbstractSheaf(X, r, c)
end

function Base.show(io::IO, F::AbstractSheaf)
  print(io, "Abstract sheaf of rank ", F.rank, " on ", F.parent)
end

ch(F::AbstractSheaf) = F.ch

function chern(F::AbstractSheaf)
  if !isdefined(F, :chern) F.chern = _expp(F.ch) end
  F.chern
end

chern(n::Int, F::AbstractSheaf) = _homog_comp(n, chern(F))
ctop(F::AbstractSheaf) = chern(F.rank, F)
segre(F::AbstractSheaf) = _inv(chern(F))
segre(n::Int, F::AbstractSheaf) = _homog_comp(n, segre(F))
todd(F::AbstractSheaf) = _todd(F.ch)

function pontryagin(F::AbstractSheaf)
  n = F.parent.dim
  x = chern(F) * chern(dual(F))
  comps = _homog_comps(0:n,x)
  sum([(-1)^i*comps[2i+1] for i in 0:n÷2])
end

pontryagin(n::Int, F::AbstractSheaf) = _homog_comp(2n, pontryagin(F))

function Oscar.chi(F::AbstractSheaf)
  X = F.parent
  integral(F.ch * todd(X)) # Hirzebruch-Riemann-Roch
end

function Oscar.chi(F::AbstractSheaf, G::AbstractSheaf)
  X = F.parent
  integral(dual(F).ch * G.ch * todd(X))
end

###############################################################################
##
##  AbstractVarietyHom
##
mutable struct AbstractVarietyHom{V1 <: AbstractVarietyT, V2 <: AbstractVarietyT}
  domain::V1
  codomain::V2
  dim::Int
  pullback::AlgHom
  pushforward::AbstractAlgebra.Generic.FunctionalMap
  O1::RingElem_dec
  T::AbstractSheaf{V1}
  function AbstractVarietyHom(X::V1, Y::V2, fˣ::AlgHom, fₓ=nothing) where {V1 <: AbstractVarietyT, V2 <: AbstractVarietyT}
    # in case the class of a point is known, fₓ can be deduced from fˣ
    # using the knowledge of a dual basis
    # and the projective formula fₓ(x⋅fˣy) = fₓ(x)⋅y
    if fₓ === nothing && isdefined(X, :point) && isdefined(Y, :point)
      b = basis(Y)
      d = dual_basis(Y)
      fₓ = x -> sum(integral(x*fˣ(y))*d[i] for (i, y) in enumerate(b))
      fₓ = map_from_func(fₓ, X.ring, Y.ring)
    end
    f = new{V1, V2}(X, Y, X.dim-Y.dim, fˣ)
    if fₓ !== nothing f.pushforward = fₓ end
    if isdefined(X, :T) && isdefined(Y, :T)
      f.T = abstract_sheaf(X, X.T.ch - fˣ(Y.T.ch))
    end
    return f
  end
end

function Oscar.hom(X::V1, Y::V2, fˣ::AlgHom, fₓ=nothing) where {V1 <: AbstractVarietyT, V2 <: AbstractVarietyT}
  AbstractVarietyHom(X, Y, fˣ, fₓ)
end

function Oscar.hom(X::V1, Y::V2, fˣ::Vector{}, fₓ=nothing) where {V1 <: AbstractVarietyT, V2 <: AbstractVarietyT}
  fˣ = hom(Y.ring, X.ring, fˣ)
  AbstractVarietyHom(X, Y, fˣ, fₓ)
end

function identity_hom(X::V) where V <: AbstractVarietyT
  hom(X, X, hom(X.ring, X.ring, gens(X.ring)), map_from_func(identity, X.ring, X.ring))
end

function Base.show(io::IO, f::AbstractVarietyHom)
  print(io, "Abstract homomorphism from ", f.domain, " to ", f.codomain)
end

Oscar.dim(f::AbstractVarietyHom) = f.dim
tangent_bundle(f::AbstractVarietyHom) = f.T
cotangent_bundle(f::AbstractVarietyHom) = dual(f.T)
todd(f::AbstractVarietyHom) = todd(f.T)

function *(f::AbstractVarietyHom, g::AbstractVarietyHom)
  X, Y = f.domain, f.codomain
  @assert g.domain == Y
  Z = g.codomain
  if isdefined(f, :pushforward) && isdefined(g, :pushforward)
    gofₓ = map_from_func(g.pushforward ∘ f.pushforward, X.ring, Z.ring)
  end
  gof = hom(X, Z, g.pullback * f.pullback, gofₓ)
  return gof
end

###############################################################################
##
##  AbstractVariety
##
mutable struct AbstractVariety <: AbstractVarietyT
  dim::Int                       # dimension
  ring::Ring_dec                 # chow ring
  base::Ring                     # coefficient ring
  point::RingElem_dec            # the class of a point
  O1::RingElem_dec               # polarization, if applicable
  T::AbstractSheaf               # tangent bundle
  bundles::Vector{AbstractSheaf} # tautological bundles, if applicable
  struct_map::AbstractVarietyHom # structure map
  @declare_other
  function AbstractVariety(n::Int, R::Ring_dec)
    base = isa(R, MPolyQuo) ? base_ring(R.R) : base_ring(R)
    X = new(n, R, base)
    # link the ring R to the variety X
    set_special(R, :variety => X)
    set_special(R, :variety_dim => n)
    return X
  end
end
abstract_variety(n::Int, R::Ring) = AbstractVariety(n, R)

# generic variety with some classes in given degrees
function abstract_variety(n::Int, symbols::Vector{String}, degs::Vector{Int}; base::Ring=QQ)
  R = filtrate(PolynomialRing(base, symbols)[1], degs)
  return abstract_variety(n, R)
end

# generic variety with some bundles in given ranks
function abstract_variety(n::Int, bundles::Vector{Pair{Int,T}}; base::Ring=QQ) where T
  symbols = vcat([[s*"$i" for i in 1:r] for (r,s) in bundles]...)
  degs = vcat([collect(1:r) for (r,s) in bundles]...)
  X = abstract_variety(n, symbols, degs, base=base)
  i = 1
  X.bundles = AbstractSheaf[]
  for (r,s) in bundles
    push!(X.bundles, abstract_sheaf(X, r, 1 + sum(gens(X.ring)[i:i+r-1])))
    i += r
  end
  return X
end

# generic variety with tangent bundle
function abstract_variety(n::Int; base::Ring=QQ)
  X = abstract_variety(n, [n=>"c"], base=base)
  X.T = X.bundles[1]
  return X
end

function Base.show(io::IO, X::AbstractVariety)
  name = get_special(X, :name)
  if name === nothing name = "Abstract variety of dim $(X.dim)" end
  print(io, name)
end

euler(X::AbstractVariety) = integral(chern(X.T))
OO(X::AbstractVariety) = abstract_sheaf(X, X.ring(1))
OO(X::AbstractVariety, n::Union{Number, RingElem}) = abstract_sheaf(X, 1, 1+n*X.O1)
Oscar.degree(X::AbstractVariety) = integral(X.O1^X.dim)
tangent_bundle(X::AbstractVariety) = X.T
cotangent_bundle(X::AbstractVariety) = dual(X.T)
canonical_class(X::AbstractVariety) = -chern(1, X.T)
canonical_bundle(X::AbstractVariety) = det(cotangent_bundle(X))
chern(X::AbstractVariety) = chern(X.T)
chern(n::Int, X::AbstractVariety) = chern(n, X.T)
todd(X::AbstractVariety) = todd(X.T)
pontryagin(X::AbstractVariety) = pontryagin(X.T)
pontryagin(n::Int, X::AbstractVariety) = pontryagin(n, X.T)

function chern_number(X::AbstractVariety, λ::Int...) chern_number(X, collect(λ)) end
function chern_number(X::AbstractVariety, λ::AbstractAlgebra.Generic.Partition) chern_number(X, collect(λ)) end
function chern_number(X::AbstractVariety, λ::Vector{Int})
  @assert sum(λ) == X.dim
  c = _homog_comps(1:X.dim, chern(X))
  integral(prod([c[i] for i in λ]))
end

function chern_numbers(X::AbstractVariety)
  c = _homog_comps(1:X.dim, chern(X))
  [integral(prod([c[i] for i in λ])) for λ in partitions(X.dim)]
end

function l_genus(k::Int, X::AbstractVariety)
  Q = X.ring
  k == 0 && return Q(1)
  R = isa(Q, MPolyQuo) ? Q.R : Q
  p = _lift(pontryagin(X.T))
  comps = _homog_comps(1:2k,p)
  Q(R(l_genus(k).f([comps[2i].f for i in 1:k]...)))
end

function l_genus(X::AbstractVariety)
  !iseven(X.dim) && error("the variety is not of even dimension")
  integral(l_genus(X.dim÷2, X))
end

function Oscar.signature(X::AbstractVariety)
  l_genus(X) # Hirzebruch signature theorem
end

function a_hat_genus(k::Int, X::AbstractVariety)
  Q = X.ring
  k == 0 && return Q(1)
  R = isa(Q, MPolyQuo) ? Q.R : Q
  p = _lift(pontryagin(X.T))
  comps = _homog_comps(1:2k,p)
  Q(R(a_hat_genus(k).f([comps[2i].f for i in 1:k]...)))
end

function a_hat_genus(X::AbstractVariety)
  !iseven(X.dim) && error("the variety is not of even dimension")
  integral(a_hat_genus(X.dim÷2, X))
end

###############################################################################
##
##  hacks for n_transExt to work;
##  should be removed once Oscar has function fields
##
# conversion between n_transExt and fmpq
(F::Singular.N_FField)(q::Union{fmpq, Rational{Int}}) = F(numerator(q))//F(denominator(q))
function (F::FlintRationalField)(x::Singular.n_transExt)
  num = Singular.n_transExt_to_spoly(Singular.numerator(x))
  cst_num = constant_coefficient(num)
  denom = Singular.n_transExt_to_spoly(Singular.denominator(x))
  cst_denom = constant_coefficient(denom)
  (num != cst_num || denom != cst_denom) && error("cannot coerce")
  F(cst_num)//F(cst_denom)
end
(F::FlintIntegerRing)(x::Singular.n_transExt) = F(QQ(x))
function Oscar.singular_ring(R::MPolyRing{Singular.n_transExt}; keep_ordering::Bool=true)
  Singular.PolynomialRing(base_ring(R), string.(R.S), ordering=ordering(R))[1]
end
# copied from mpoly.jl to avoid ambiguity for n_transExt
function (Ox::AbstractAlgebra.Generic.MPolyRing{Singular.n_transExt})(f::Singular.spoly{Singular.n_transExt})
  O = base_ring(Ox)
  Sx = parent(f)
  @assert ngens(Sx) == ngens(Ox)
  g = MPolyBuildCtx(Ox)
  for (c, e) = Base.Iterators.zip(Singular.coefficients(f), Singular.exponent_vectors(f))
    push_term!(g, O(c), e)
  end
  return finish(g)
end
(W::Oscar.MPolyRing_dec{Singular.n_transExt})(f::Singular.spoly{Singular.n_transExt}) = Oscar.MPolyElem_dec(W.R(f), W)
##
###############################################################################

# the Hilbert polynomial depends on the O(1) chosen
# so if X.O1 has been changed, it needs to be computed again
# 
# also the chow ring needs to be reconstructed using the function field,
# so this is probably slower than starting with `base=F` where F is a function
# field QQ(n) and use directly `chi(OO(x,n))`
function Oscar.hilbert_polynomial(X::AbstractVariety)
  # first coerce the coefficient ring to QQ then extend to QQ(t)
  Qt, (t,) = Singular.FunctionField(Singular.QQ, ["t"])
  Qt_R = parent(change_base_ring(Qt, X.ring.R().f))
  R = filtrate(Qt_R, X.ring.R.d, X.ring.R.lt)
  toQQ = x -> change_base_ring(QQ, _lift(x).f)
  toR = x -> R(change_base_ring(Qt, toQQ(x), parent=Qt_R))
  I = ideal(toR.(gens(X.ring.I)))
  Q, toQ = quo(R, I)
  set_special(Q, :variety_dim => X.dim)
  ch_O_t = 1 + _logg(1 + t * toQ(toR(X.O1)))
  td = toQ(toR(todd(X)))
  pt = toQ(toR(X.point))
  hilb = constant_coefficient(div(_lift(ch_O_t * td), _lift(pt)))
  # convert back to an Oscar polynomial
  denom = Singular.n_transExt_to_spoly(Singular.denominator(hilb))
  denom = QQ(constant_coefficient(denom))
  return 1//denom * change_base_ring(QQ, Singular.n_transExt_to_spoly(hilb))
end

###############################################################################
##
##  Utilities
##
function Oscar.basis(X::AbstractVariety)
  Q = X.ring
  Q.(Oscar._kbase(Q))
end

function Oscar.basis(k::Int, X::AbstractVariety)
  basis_by_degree(X)[k+1]
end

function basis_by_degree(X::AbstractVariety)
  n = X.dim
  b = basis(X)
  ans = [elem_type(X.ring)[] for i in 0:n]
  for bi in b
    d = Int(degree(bi)[1])
    push!(ans[d+1], bi)
  end
  ans
end

function betti(X::AbstractVariety)
  length.(basis_by_degree(X))
end

function _simplify(x::MPolyQuoElem) simplify(x) end
function _simplify(x::MPolyElem) x end

function _lift(x::MPolyQuoElem) lift(simplify(x)) end
function _lift(x::MPolyElem) x end

function _homog_comp(n::Int, x::MPolyQuoElem)
  Q = parent(x)
  Q(homogenous_component(x, Q.R.D([n])))
end

function _homog_comp(n::Int, x::MPolyElem)
  R = parent(x)
  homogenous_component(x, R.D([n]))
end

# TODO this seems to be very inefficient!
function _homog_comps(I::UnitRange, x::MPolyQuoElem)
  Q = parent(x)
  D = Q.R.D
  comps = homogenous_components(x) 
  [D([n]) in keys(comps) ? Q(comps[D([n])]) : Q(0) for n in I]
end

function _homog_comps(I::UnitRange, x::MPolyElem)
  D = parent(x).D
  comps = homogenous_components(x) 
  [D([n]) in keys(comps) ? comps[D([n])] : parent(x)(0) for n in I]
end

function Oscar.integral(x::Union{MPolyElem, MPolyQuoElem}; bott::Bool=false)
  X = get_special(parent(x), :variety)
  if bott # convert to a Grassmannian with T-action and use the Bott's formula
    get_special(X, :grassmannian) !== :absolute && error("the variety is not a Grassmannian")
    if get_special(X, :bott) === nothing
      k = X.bundles[1].rank
      n = k + X.bundles[2].rank
      set_special(X, :bott => grassmannian(k, n, bott=true))
    end
    G = get_special(X, :bott)
    S = G.bundles[1]
    x = _homog_comp(X.dim, x)
    return integral(chern(S, x.f))
  elseif isdefined(X, :point)
    return constant_coefficient(div(_lift(x), _lift(X.point)))
  else
    return _homog_comp(X.dim, x)
  end
end

function intersection_matrix(X::AbstractVariety) intersection_matrix(basis(X)) end
function intersection_matrix(a::Vector{}, b=nothing)
  if b === nothing b = a end
  matrix(QQ, [integral(ai*bj) for ai in a, bj in b])
end

function dual_basis(X::AbstractVariety)
  n = X.dim
  ans = Dict{RingElem_dec, RingElem_dec}()
  B = basis(X)
  # find dual using only classes in complementary dimensions
  Bd = basis_by_degree(X)
  for (i,b) in enumerate(Bd)
    l = length(b)
    comp = Bd[n+2-i]
    d = Matrix(inv(intersection_matrix(comp, b))) * comp
    for (j,bj) in enumerate(b)
      ans[bj] = d[j]
    end
  end
  [ans[B[i]] for i in 1:length(B)]
end

###############################################################################
##
##  Operators
##
function pullback(f::AbstractVarietyHom, x::RingElem_dec)
  _simplify(f.pullback(x))
end

function pullback(f::AbstractVarietyHom, F::AbstractSheaf)
  abstract_sheaf(f.domain, pullback(f, F.ch))
end

function pullback(f::AbstractVarietyHom, x::Vector{})
  [pullback(f, xi) for xi in x]
end

function pushforward(f::AbstractVarietyHom, x::RingElem_dec)
  _simplify(f.pushforward(x))
end

function pushforward(f::AbstractVarietyHom, F::AbstractSheaf)
  abstract_sheaf(Y, pushforward(f, F.ch * todd(f))) # Grothendieck-Hirzebruch-Riemann-Roch
end

function pushforward(f::AbstractVarietyHom, x::Vector{})
  [pushforward(f, xi) for xi in x]
end

function Oscar.hom(X::AbstractVariety, Y::AbstractVariety)
  X == Y && return identity_hom(X)
  homs = AbstractVarietyHom[]
  # follow the chain of structure maps to see if we can arrive at Y
  while isdefined(X, :struct_map) && X != Y
    push!(homs, X.struct_map)
    X = X.struct_map.codomain
  end
  X != Y && error("no canonical homomorphism between the given varieties")
  return reduce(*, homs)
end
→(X::AbstractVariety, Y::AbstractVariety) = hom(X, Y)
/(X::AbstractVariety, Y::AbstractVariety) = hom(X, Y) # following Macaulay2

# product variety
function *(X::AbstractVariety, Y::AbstractVariety)
  @assert X.base == Y.base
  base = X.base
  A, B = X.ring, Y.ring
  AA, AI = isa(A, MPolyQuo) ? (A.R, A.I) : (A, ideal([A(0)]))
  BB, BI = isa(B, MPolyQuo) ? (B.R, B.I) : (B, ideal([B(0)]))
  Z = AA.D # needs to convert the gradings of B into A
  symsA, degsA = string.(AA.R.S), AA.d
  a, b = ngens(AA), ngens(BB)
  symsB, degsB = string.(BB.R.S), [Z([Int(d[1])]) for d in BB.d]
  R = filtrate(PolynomialRing(base, vcat(symsA, symsB))[1], vcat(degsA, degsB), AA.lt)
  AtoR = hom(AA, R, gens(R)[1:a])
  BtoR = hom(BB, R, gens(R)[a+1:end])
  IA = ideal(AtoR.(gens(AI)))
  IB = ideal(BtoR.(gens(BI)))
  Q, toQ = quo(R, IA+IB)
  XY = abstract_variety(X.dim+Y.dim, Q)
  if isdefined(X, :point) && isdefined(Y, :point)
    XY.point = toQ(AtoR(_lift(X.point)) * BtoR(_lift(Y.point)))
  end
  if isdefined(X, :T) && isdefined(Y, :T)
    XY.T = abstract_sheaf(XY, toQ(AtoR(_lift(X.T.ch)) + BtoR(_lift(Y.T.ch))))
  end
  if isdefined(X, :O1) && isdefined(Y, :O1) # Segre embedding
    XY.O1 = toQ(AtoR(_lift(X.O1)) + BtoR(_lift(Y.O1)))
  end
  p = hom(XY, X, gens(Q)[1:a])
  q = hom(XY, Y, gens(Q)[a+1:end])
  return XY, (p, q)
end

function adams(k::Int, x::RingElem_dec)
  d = Int(degree(x)[1])
  comps = _homog_comps(0:d,x)
  sum([ZZ(k)^i*comps[i+1] for i in 0:d])
end

function Oscar.dual(F::AbstractSheaf)
  abstract_sheaf(F.parent, adams(-1, F.ch))
end

+(n::Union{Number,RingElem}, F::AbstractSheaf) = abstract_sheaf(F.parent, n + F.ch)
*(n::Union{Number,RingElem}, F::AbstractSheaf) = abstract_sheaf(F.parent, n * F.ch)
+(F::AbstractSheaf, n::Union{Number,RingElem}) = n + F
*(F::AbstractSheaf, n::Union{Number,RingElem}) = n * F
-(F::AbstractSheaf) = abstract_sheaf(F.parent, -F.ch)
det(F::AbstractSheaf) = abstract_sheaf(F.parent, 1, 1+_homog_comp(1, F.ch))

# try to pullback to the same variety
function _coerce(F::AbstractSheaf, G::AbstractSheaf)
  X, Y = F.parent, G.parent
  X == Y && return F, G
  try
    return F, pullback(X → Y, G)
  catch
    try
      return pullback(Y → X, F), G
    catch
      error("the sheaves are not on compatible varieties")
    end
  end
end

function +(F::AbstractSheaf, G::AbstractSheaf)
  F, G = _coerce(F, G)
  abstract_sheaf(F.parent, _simplify(F.ch + G.ch))
end

function -(F::AbstractSheaf, G::AbstractSheaf)
  F, G = _coerce(F, G)
  abstract_sheaf(F.parent, _simplify(F.ch - G.ch))
end

function *(F::AbstractSheaf, G::AbstractSheaf)
  F, G = _coerce(F, G)
  abstract_sheaf(F.parent, _simplify(F.ch * G.ch))
end

⊕(F::AbstractSheaf, G::AbstractSheaf) = F + G
⊗(F::AbstractSheaf, G::AbstractSheaf) = F * G
Oscar.hom(F::AbstractSheaf, G::AbstractSheaf) = dual(F) * G

function exterior_power(k::Int, F::AbstractSheaf)
  abstract_sheaf(F.parent, _wedge(k, F.ch)[end])
end

function symmetric_power(k::Int, F::AbstractSheaf)
  abstract_sheaf(F.parent, _sym(k, F.ch)[end])
end

function symmetric_power(k::RingElem, F::AbstractSheaf)
  X = F.parent
  PF = proj(dual(F))
  p = PF.struct_map
  abstract_sheaf(X, pushforward(p, sum(_homog_comps(0:PF.dim, OO(PF, k).ch * todd(p)))))
end

function schur_functor(λ::Vector{Int}, F::AbstractSheaf) schur_functor(Partition(λ), F) end
function schur_functor(λ::AbstractAlgebra.Generic.Partition, F::AbstractSheaf)
  λ = conj(λ)
  X = F.parent
  w = _wedge(sum(λ), F.ch)
  S, ei = PolynomialRing(QQ, ["e$i" for i in 1:length(w)])
  e = i -> (i < 0) ? S(0) : ei[i+1]
  M = [e(λ[i]-i+j) for i in 1:length(λ), j in 1:length(λ)]
  sch = det(matrix(S, M)) # Jacobi-Trudi
  abstract_sheaf(X, X.ring(sch([isa(wi, MPolyQuoElem) ? wi : wi.f for wi in w]...)))
end

function giambelli(λ::Vector{Int}, F::AbstractSheaf)
  Q = F.parent.ring
  R = isa(Q, MPolyQuo) ? Q.R : Q
  M = [_lift(chern(λ[i]-i+j, F)) for i in 1:length(λ), j in 1:length(λ)]
  Q(det(matrix(R, M)))
end

function _expp(x::RingElem_dec)
  Q = parent(x)
  n = get_special(Q, :variety_dim)
  comps = _homog_comps(0:n,x)
  p = [(-1)^i*factorial(ZZ(i))*comps[i+1] for i in 0:n]
  e = repeat([Q(0)], n+1)
  e[1] = Q(1)
  for i in 1:n
    e[i+1] = -1//ZZ(i) * sum(p[j+1] * e[i-j+1] for j in 1:i)
  end
  _simplify(sum(e))
end

function _logg(x::RingElem_dec)
  Q = parent(x)
  n = get_special(Q, :variety_dim)
  p = repeat([Q(0)], n+1)
  e = _homog_comps(0:n,x)
  for i in 1:n
    p[i+1] = -ZZ(i)*e[i+1] - sum([e[j+1] * p[i-j+1] for j in 1:i-1], init=Q(0))
  end
  _simplify(sum([(-1)^i//factorial(ZZ(i))*p[i+1] for i in 1:n], init=Q(0)))
end

function _inv(x::RingElem_dec)
  Q = parent(x)
  n = get_special(Q, :variety_dim)
  R = isa(Q, MPolyQuo) ? Q.R : Q
  S, t = PowerSeriesRing(R.R, n+1, "t")
  comps = _homog_comps(0:n,_lift(x))
  c = sum([t^i * comps[i+1].f for i in 0:n])
  s = inv(c)
  _simplify(Q(R(sum(coeff(s, i) for i in 0:n))))
end

# returns all the wedge from 0 to k
function _wedge(k::Int, x::RingElem_dec)
  Q = parent(x)
  k == 0 && return [Q(1)]
  n = get_special(Q, :variety_dim)
  R = isa(Q, MPolyQuo) ? Q.R : Q
  wedge = repeat([R[0]], k+1)
  wedge[1] = R(1)
  wedge[2] = _lift(x)
  for j in 2:k
    wedge[j+1] = 1//ZZ(j) * sum(_homog_comps(0:n, sum((-1)^(j-i+1) * wedge[i+1] * adams(j-i, _lift(x)) for i in 0:j-1)))
  end
  Q.(wedge)
end

# returns all the sym from 0 to k
function _sym(k::Int, x::RingElem_dec)
  Q = parent(x)
  k == 0 && return [Q(1)]
  n = get_special(Q, :variety_dim)
  R = isa(Q, MPolyQuo) ? Q.R : Q
  r = min(k, Int(ZZ(constant_coefficient(_lift(x)))))
  wedge = _wedge(r, x)
  sym = repeat([R[0]], k+1)
  sym[1] = R(1)
  sym[2] = _lift(x)
  for j in 2:k
    sym[j+1] = sum(_homog_comps(0:n, sum((-1)^(i+1) * _lift(wedge[i+1]) * sym[j-i+1] for i in 1:min(j,r))))
  end
  Q.(sym)
end

# returns the genus w.r.t. a given Taylor series
function _genus(x::RingElem_dec, taylor::Vector{})
  Q = parent(x)
  x == 0 && return Q(1)
  n = get_special(Q, :variety_dim)
  R = filtrate(PolynomialRing(QQ, ["t"])[1])
  set_special(R, :variety_dim => n)
  t = gens(R)[1]
  lg = _logg(sum(taylor[i+1] * t^i for i in 0:n))
  comps = _homog_comps(1:n,lg)
  lg = [leading_coefficient(comps[i]) for i in 1:n]
  comps = _homog_comps(1:n,x)
  _expp(sum(factorial(ZZ(i)) * lg[i] * comps[i] for i in 1:n))
end

function _todd(x::RingElem_dec)
  n = get_special(parent(x), :variety_dim)
  # the Taylor series of t/(1-exp(-t))
  taylor = [(-1)^i//factorial(ZZ(i))*bernoulli(i) for i in 0:n]
  _genus(x, taylor)
end

function _l_genus(x::RingElem_dec)
  n = get_special(parent(x), :variety_dim)
  # the Taylor series of sqrt(t)/tanh(sqrt(t))
  taylor = [ZZ(2)^2i//factorial(ZZ(2i))*bernoulli(2i) for i in 0:n]
  _genus(x, taylor)
end

function _a_hat_genus(x::RingElem_dec)
  n = get_special(parent(x), :variety_dim)
  # the Taylor series of (sqrt(t)/2)/sinh(sqrt(t)/2)
  R, t = PowerSeriesRing(QQ, 2n+1, "t")
  s = divexact(t, exp(QQ(1//2)*t)-exp(-QQ(1//2)*t))
  taylor = [coeff(s, 2i) for i in 0:n]
  _genus(x, taylor)
end

# returns the formulae symbolically
function todd(n::Int)
  n == 0 && return QQ(1)
  R = filtrate(PolynomialRing(QQ, ["c$i" for i in 1:n])[1], collect(1:n))
  set_special(R, :variety_dim => n)
  c = 1 + sum(R[i] for i in 1:n)
  _homog_comp(n, _todd(_logg(c)))
end

function l_genus(n::Int)
  n == 0 && return QQ(1)
  R = filtrate(PolynomialRing(QQ, ["p$i" for i in 1:n])[1], collect(1:n))
  set_special(R, :variety_dim => n)
  p = 1 + sum(R[i] for i in 1:n)
  _homog_comp(n, _l_genus(_logg(p)))
end

function a_hat_genus(n::Int)
  n == 0 && return QQ(1)
  R = filtrate(PolynomialRing(QQ, ["p$i" for i in 1:n])[1], collect(1:n))
  set_special(R, :variety_dim => n)
  p = 1 + sum(R[i] for i in 1:n)
  _homog_comp(n, _a_hat_genus(_logg(p)))
end

function section_zero_locus(F::AbstractSheaf; class::Bool=false)
  X = F.parent
  Q = X.ring
  cZ = ctop(F)
  # return only the class of Z in the chow ring of X
  class && return cZ
  I = quotient(Q.I, ideal([lift(cZ)]))
  RZ, toRZ = quo(Q.R, I)
  Z = abstract_variety(X.dim - F.rank, RZ)
  if isdefined(X, :point)
    ps = basis(Z.dim, Z) # the 0-cycles
    @assert length(ps) == 1 # make sure that the 0-cycle is unique
    p = ps[1]
    degp = integral(Q(lift(p)) * cZ) # compute the degree of iₓp
    # use `inv` so that it remains in the base ring
    idegp = inv(degp)
    @assert idegp * degp == 1
    Z.point = idegp * p
  end
  if isdefined(X, :T)
    Z.T = abstract_sheaf(Z, toRZ(lift(X.T.ch - F.ch)))
  end
  if isdefined(X, :O1)
    Z.O1 = simplify(toRZ(lift(X.O1)))
  end
  iₓ = x -> (Q(lift(x)) * cZ)
  iₓ = map_from_func(iₓ, Z.ring, X.ring)
  i = hom(Z, X, toRZ.(lift.(gens(Q))), iₓ)
  i.T = pullback(i, -F)
  Z.struct_map = i
  return Z
end

function degeneracy_locus(k::Int, F::AbstractSheaf, G::AbstractSheaf; class=false)
  F, G = _coerce(F, G)
  m, n = rank(F), rank(G)
  @assert k < min(m,n)
  if class
    # return only the class of D in the chow ring of X
    if (m-k)*(n-k) <= F.parent.dim
      return _homog_comp((m-k)*(n-k), ch(schur_functor(repeat([m-k], n-k), G-F)))
    else # expected dimension is negative
      return F.parent.ring(0)
    end
  end
  Gr = (m-k == 1) ? proj(F) : flag(F, m-k, m)
  S = Gr.bundles[1]
  D = section_zero_locus(hom(S, G))
  D.struct_map = hom(D, F.parent) # skip the flag variety
  return D
end

###############################################################################
##
##  TODO Blowup
##
# function blowup(i::AbstractVarietyHom)
# end

###############################################################################
##
##  Projective spaces, Grassmannians, flag varieties
##
# Projective spaces and projective bundles parametrize 1-dim *subspaces*
function proj(n::Int; base::Ring=QQ, symbol::String="h")
  R = filtrate(PolynomialRing(base, [symbol])[1], [1])
  h = gens(R)[1]
  I = ideal([h^(n+1)])
  Q, _ = quo(R, I)
  h = gens(Q)[1]
  P = abstract_variety(n, Q)
  P.point = h^n
  P.O1 = h
  chTP = Q(n)
  for i in 1:n
    chTP += ZZ(n+1)//factorial(ZZ(i))*Q[1]^i
  end
  P.T = abstract_sheaf(P, chTP)
  P.T.chern = (1+h)^(n+1) - h^(n+1)
  S = abstract_sheaf(P, 1, 1-h)
  Q = OO(P)*(n+1) - S
  P.bundles = [S, Q]
  P.struct_map = hom(P, point(base), [P.ring(1)])
  set_special(P, :name => "Abstract projective space of dim $n")
  set_special(P, :grassmannian => :absolute)
  return P
end

function proj(F::AbstractSheaf; symbol::String="h")
  X, r = F.parent, F.rank
  !isa(r, Int) && error("expect rank to be an integer")
  n, Q = X.dim, X.ring
  R, I = isa(Q, MPolyQuo) ? (Q.R, Q.I) : (Q, ideal([Q(0)]))
  symbols = vcat([symbol], string.(R.R.S))
  degs = vcat([R.D([1])], R.d)
  # construct the ring
  R1 = filtrate(PolynomialRing(X.base, symbols)[1], degs, R.lt)
  h = gens(R1)[1]
  pback = hom(R, R1, gens(R1)[2:end])
  pfwd = hom(R1, Q, vcat([Q(0)], gens(Q)))
  # construct the ideal
  I1 = ideal(vcat(pback.(gens(I)), [sum(h^(r-i) * pback(_lift(chern(i, F))) for i in 0:r)]))
  Q1, toQ1 = quo(R1, I1)
  h = gens(Q1)[1]
  # construct the variety
  PF = abstract_variety(n+r-1, Q1)
  pˣ = hom(X.ring, Q1, gens(Q1)[2:end])
  pₓ = x -> pfwd(div(_lift(x), _lift(h^(r-1))))
  pₓ = map_from_func(pₓ, PF.ring, X.ring)
  p = hom(PF, X, pˣ, pₓ)
  if isdefined(X, :point)
    PF.point = pˣ(X.point) * h^(r-1)
  end
  p.O1 = h
  PF.O1 = h
  S = abstract_sheaf(PF, 1, 1-h)
  Q = pullback(p, F) - S
  p.T = dual(S)*Q
  if isdefined(X, :T)
    PF.T = pullback(p, X.T) + p.T
  end
  PF.bundles = [S, Q]
  PF.struct_map = p
  set_special(PF, :name => "Projectivization of $F")
  set_special(PF, :grassmannian => :relative)
  return PF
end

function grassmannian(k::Int, n::Int; base::Ring=QQ, bott::Bool=false, symbol::String="c")
  bott && return BottLocalization.grassmannian(k, n)
  @assert k < n
  R = filtrate(PolynomialRing(base, ["c$i" for i in 1:k])[1], collect(1:k))
  c = gens(R)
  ic = sum(_lift(-sum(c))^i for i in 1:n) # since c(S)⋅c(Q) = 1, this gives c(Q)
  I = ideal(_homog_comps(n-k+1:n, ic)) # conditions given by rank(Q) = n-k
  Q, toQ = quo(R, I)
  Gr = abstract_variety(k*(n-k), Q)
  Gr.O1 = -Q[1]
  S = abstract_sheaf(Gr, k, toQ(1+sum(c)))
  Q = OO(Gr)*n - S
  Gr.point = toQ((-1)^(k*(n-k))*c[end]^(n-k))
  Gr.T = dual(S) * Q
  Gr.bundles = [S, Q]
  Gr.struct_map = hom(Gr, point(base), [Gr.ring(1)])
  set_special(Gr, :name => "Abstract Grassmannian Gr($k, $n)")
  set_special(Gr, :grassmannian => :absolute)
  return Gr
end

function flag(dims::Int...; base::Ring=QQ, bott::Bool=false, symbol::String="c")
  flag(collect(dims), base=base, bott=bott)
end
function flag(dims::Vector{Int}; base::Ring=QQ, bott::Bool=false, symbol::String="c")
  bott && return BottLocalization.flag(dims)
  n, l = dims[end], length(dims)
  ranks = pushfirst!([dims[i+1]-dims[i] for i in 1:l-1], dims[1])
  @assert all(r->r>0, ranks)
  syms = vcat([["c$i$j" for j in 1:r] for (i,r) in enumerate(ranks)]...)
  degs = vcat([collect(1:r) for r in ranks]...)
  R = filtrate(PolynomialRing(base, syms)[1], degs)
  c = pushfirst!([1+sum(gens(R)[dims[i]+1:dims[i+1]]) for i in 1:l-1], 1+sum(gens(R)[1:dims[1]]))
  prod_c = prod(c)
  Rx, x = R.R["x"]
  gi = _homog_comps(0:n, prod_c)
  g = sum(gi[i+1].f * x^(n-i) for i in 0:n)
  rels = R(Rx(rem(x^n, g))(1))
  I = ideal(_homog_comps(1:n, rels))
  Q, toQ = quo(R, I)
  d = sum(ranks[i] * sum(dims[end]-dims[i]) for i in 1:l-1)
  Fl = abstract_variety(d, Q)
  Fl.bundles = [abstract_sheaf(Fl, r, toQ(ci)) for (r,ci) in zip(ranks, c)]
  Fl.O1 = sum((i-1)*chern(1, Fl.bundles[i]) for i in 1:l)
  Fl.point = prod(ctop(E)^sum(dims[i]) for (i,E) in enumerate(Fl.bundles[2:end]))
  Fl.T = sum(dual(Fl.bundles[i]) * sum([Fl.bundles[j] for j in i+1:l]) for i in 1:l-1)
  Fl.struct_map = hom(Fl, point(base), [Fl.ring(1)])
  set_special(Fl, :name => "Abstract flag variety Flag$(tuple(dims...))")
  if l == 2 set_special(Fl, :grassmannian => :absolute) end
  return Fl
end

function flag(k::Int, F::AbstractSheaf; symbol::String="c") flag([k], F, symbol=symbol) end
function flag(dims::Vector{Int}, F::AbstractSheaf; symbol::String="c")
  X, n = F.parent, F.rank
  # compute the ranks and relative dim
  l = length(dims)
  ranks = pushfirst!([dims[i+1]-dims[i] for i in 1:l-1], dims[1])
  @assert all(r->r>0, ranks) && dims[end] <= n
  if dims[end] < n # the last dim can be omitted
    push!(dims, n)
    push!(ranks, n-dims[l])
    l += 1
  end
  d = sum(ranks[i] * sum(dims[end]-dims[i]) for i in 1:l-1)
  # construct the ring
  Q = X.ring
  R, I = isa(Q, MPolyQuo) ? (Q.R, Q.I) : (Q, ideal([Q(0)]))
  syms = vcat([[symbol*"$i$j" for j in 1:r] for (i,r) in enumerate(ranks)]..., string.(R.R.S))
  degs = vcat([R.D([i]) for r in ranks for i in 1:r], R.d)
  R1 = filtrate(PolynomialRing(X.base, syms)[1], degs, R.lt)
  pback = hom(R, R1, gens(R1)[end-ngens(R)+1:end])
  pfwd = hom(R1, Q, vcat(repeat([Q(0)], ngens(R1)-ngens(Q)), gens(Q)))
  # compute the relations
  c = pushfirst!([1+sum(gens(R1)[dims[i]+1:dims[i+1]]) for i in 1:l-1], 1+sum(gens(R1)[1:dims[1]]))
  prod_c = prod(c)
  Rx, x = R1.R["x"]
  fi = _homog_comps(0:n, pback(_lift(chern(F))))
  f = sum(fi[i+1].f * x^(n-i) for i in 0:n)
  gi = _homog_comps(0:n, prod_c)
  g = sum(gi[i+1].f * x^(n-i) for i in 0:n)
  rels = R1(Rx(rem(f, g))(1))
  I1 = ideal(vcat(pback.(gens(I)), _homog_comps(1:n, rels)))
  Q1, toQ1 = quo(R1, I1)
  Fl = abstract_variety(X.dim + d, Q1)
  Fl.bundles = [abstract_sheaf(Fl, r, toQ1(ci)) for (r,ci) in zip(ranks, c)]
  section = prod(ctop(E)^sum(dims[i]) for (i, E) in enumerate(Fl.bundles[2:end]))
  pˣ = hom(Q, Q1, gens(Q1)[end-ngens(Q)+1:end])
  # TODO needs the block ordering to get the correct result
  # is there a workaround?
  pₓ = x -> (@warn "the result may be wrong"; pfwd(div(_lift(x), _lift(section))))
  pₓ = map_from_func(pₓ, Fl.ring, X.ring)
  if isdefined(X, :point)
    Fl.point = pˣ(X.point) * section
    p = hom(Fl, X, pˣ) # in this case pₓ is not needed
  else
    p = hom(Fl, X, pˣ, pₓ)
  end
  p.O1 = simplify(sum((i-1)*chern(1, Fl.bundles[i]) for i in 1:l))
  Fl.O1 = p.O1
  p.T = sum(dual(Fl.bundles[i]) * sum([Fl.bundles[j] for j in i+1:l]) for i in 1:l-1)
  if isdefined(X, :T)
    Fl.T = pullback(p, X.T) + p.T
  end
  Fl.struct_map = p
  set_special(Fl, :name => "Relative flag variety Flag$(tuple(dims...)) for $F")
  set_special(Fl, :section => section)
  if l == 2 set_special(Fl, :grassmannian => :relative) end
  return Fl
end

function schubert_class(G::AbstractVariety, λ::Int...) schubert_class(G, collect(λ)) end
function schubert_class(G::AbstractVariety, λ::AbstractAlgebra.Generic.Partition) schubert_class(G, collect(λ)) end
function schubert_class(G::AbstractVariety, λ::Vector{Int})
  get_special(G, :grassmannian) === nothing && error("the variety is not a Grassmannian")
  (length(λ) > rank(G.bundles[1]) || sort(λ, rev=true) != λ) && error("the Schubert input is not well-formed")
  giambelli(λ, G.bundles[2])
end

# partitions of n with at most k numbers each ≤ m
function partitions(n::Int, k::Int=n, m::Int=-1)
  ans = AbstractAlgebra.Generic.Partition[]
  (n > 0 && k == 0) && return ans
  if m < 0 m = n end
  n <= m && push!(ans, Partition(n > 0 ? [n] : Int[]))
  for v in Int(min(n-1,m)):-1:1
    for p in partitions(n-v, k-1, v)
      push!(ans, Partition(pushfirst!(collect(p), v)))
    end
  end
  ans
end

function schubert_classes(m::Int, G::AbstractVariety)
  get_special(G, :grassmannian) === nothing && error("the variety is not a Grassmannian")
  S, Q = G.bundles
  [schubert_class(G, λ) for λ in partitions(m, rank(S), rank(Q))]
end

function complete_intersection(P::AbstractVariety, degs::Int...) complete_intersection(P, collect(degs)) end
function complete_intersection(P::AbstractVariety, degs::Vector{Int})
  section_zero_locus(sum(OO(P, d) for d in degs))
end

function point(base=QQ)
  R = filtrate(PolynomialRing(base, ["p"])[1], [0])
  p = gens(R)[1]
  I = ideal([p-1])
  Q, _ = quo(R, I)
  pt = abstract_variety(0, Q)
  pt.point = Q(1)
  pt.T = abstract_sheaf(pt, Q(0))
  pt.O1 = Q(0)
  set_special(pt, :name => "Point")
  return pt
end

# function hom_to_point(X::AbstractVariety)
#   hom(X, point(X.base), [X.ring(1)])
# end

end # module
using .Intersection
