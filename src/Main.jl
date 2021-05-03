abstract type AbsVarietyT <: Variety end

###############################################################################
#
# AbsSheaf
#
mutable struct AbsSheaf{V <: AbsVarietyT} <: Sheaf
  parent::V
  rank::Union{Int, RingElem}
  ch::ChRingElem
  chern::ChRingElem
  function AbsSheaf(X::V, ch::RingElem) where V <: AbsVarietyT
    AbsSheaf(X, X.ring(ch))
  end
  function AbsSheaf(X::V, r::Scalar, c::RingElem) where V <: AbsVarietyT
    AbsSheaf(X, r, X.ring(c))
  end
  function AbsSheaf(X::V, ch::ChRingElem) where V <: AbsVarietyT
    ch = simplify(ch)
    r = constant_coefficient(ch.f)
    try r = Int(Singular.ZZ(Singular.QQ(r)))
    catch # r can contain symbolic variables
    end
    new{V}(X, r, ch)
  end
  function AbsSheaf(X::V, r::Scalar, c::ChRingElem) where V <: AbsVarietyT
    new{V}(X, r, r + _logg(c), c)
  end
end
sheaf(X::V, ch::RingElem) where V <: AbsVarietyT = AbsSheaf(X, ch)
sheaf(X::V, ch::ChRingElem) where V <: AbsVarietyT = AbsSheaf(X, ch)
sheaf(X::V, r::Scalar, c::RingElem) where V <: AbsVarietyT = AbsSheaf(X, r, c)
sheaf(X::V, r::Scalar, c::ChRingElem) where V <: AbsVarietyT = AbsSheaf(X, r, c)

==(F::AbsSheaf, G::AbsSheaf) = F.ch == G.ch

ch(F::AbsSheaf) = F.ch
chern(F::AbsSheaf) = (
  if !isdefined(F, :chern) F.chern = _expp(F.ch) end;
  F.chern)
chern(n::Int, F::AbsSheaf) = chern(F)[n]
ctop(F::AbsSheaf) = chern(F.rank, F)
segre(F::AbsSheaf) = inv(chern(F))
segre(n::Int, F::AbsSheaf) = segre(F)[n]
todd(F::AbsSheaf) = _todd(F.ch)

function pontryagin(F::AbsSheaf)
  n = F.parent.dim
  x = chern(F) * chern(dual(F))
  comps = x[0:n]
  sum([(-1)^i*comps[2i+1] for i in 0:n÷2])
end

pontryagin(n::Int, F::AbsSheaf) = pontryagin(F)[2n]

chi(F::AbsSheaf) = integral(F.ch * todd(F.parent)) # Hirzebruch-Riemann-Roch
chi(F::AbsSheaf, G::AbsSheaf) = begin
  F, G = _coerce(F, G)
  integral(dual(F).ch * G.ch * todd(F.parent))
end

###############################################################################
#
# AbsVarietyHom
#
mutable struct AbsVarietyHom{V1 <: AbsVarietyT, V2 <: AbsVarietyT} <: VarietyHom
  domain::V1
  codomain::V2
  dim::Int
  pullback::ChAlgHom
  pushforward::FunctionalMap
  O1::ChRingElem
  T::AbsSheaf{V1}
  function AbsVarietyHom(X::V1, Y::V2, fˣ::ChAlgHom, fₓ=nothing) where {V1 <: AbsVarietyT, V2 <: AbsVarietyT}
    if fₓ === nothing && get_special(X, :point) !== nothing && isdefined(Y, :point)
      fₓ = x -> integral(x) * Y.point
      fₓ = map_from_func(fₓ, X.ring, Y.ring)
    end
    if fₓ === nothing && isdefined(X, :point) && isdefined(Y, :point)
      b = basis(Y)
      d = dual_basis(Y)
      fₓ = x -> (
	if dim(Y) >= 2 && get_special(Y, :alg) === nothing
	  @warn "assuming that all algebraic classes are known for\n$Y\notherwise the result may be wrong" end;
	sum(integral(x*fˣ(y))*d[i] for (i, y) in enumerate(b)))
      fₓ = map_from_func(fₓ, X.ring, Y.ring)
    end
    f = new{V1, V2}(X, Y, X.dim-Y.dim, fˣ)
    if fₓ !== nothing f.pushforward = fₓ end
    if isdefined(X, :T) && isdefined(Y, :T)
      f.T = AbsSheaf(X, X.T.ch - fˣ(Y.T.ch))
    end
    return f
  end
  function AbsVarietyHom(X::V1, Y::V2, l::Vector, fₓ=nothing) where {V1 <: AbsVarietyT, V2 <: AbsVarietyT}
    fˣ = ChAlgHom(Y.ring, X.ring, l)
    AbsVarietyHom(X, Y, fˣ, fₓ)
  end
end
function hom(X::V1, Y::V2, l::Vector, fₓ=nothing; inclusion::Bool = false) where {V1 <: AbsVarietyT, V2 <: AbsVarietyT}
  !inclusion && return AbsVarietyHom(X, Y, l, fₓ)
  _inclusion(AbsVarietyHom(X, Y, l))
end

dim(f::AbsVarietyHom) = f.dim
tangent_bundle(f::AbsVarietyHom) = f.T
cotangent_bundle(f::AbsVarietyHom) = dual(f.T)
todd(f::AbsVarietyHom) = todd(f.T)
pullback(f::AbsVarietyHom, x::ChRingElem) = f.pullback(x)
pushforward(f::AbsVarietyHom, x::ChRingElem) = f.pushforward(x)
pullback(f::AbsVarietyHom, F::AbsSheaf) = AbsSheaf(f.domain, f.pullback(F.ch))
pushforward(f::AbsVarietyHom, F::AbsSheaf) = AbsSheaf(f.codomain, f.pushforward(F.ch * todd(f))) # Grothendieck-Hirzebruch-Riemann-Roch

function identity_hom(X::V) where V <: AbsVarietyT
  AbsVarietyHom(X, X, X.(gens(X.ring.R)), map_from_func(identity, X.ring, X.ring))
end
function *(f::AbsVarietyHom, g::AbsVarietyHom)
  X, Y = f.domain, f.codomain
  @assert g.domain == Y
  Z = g.codomain
  gofₓ = nothing
  if isdefined(f, :pushforward) && isdefined(g, :pushforward)
    gofₓ = map_from_func(g.pushforward ∘ f.pushforward, X.ring, Z.ring)
  end
  gof = AbsVarietyHom(X, Z, g.pullback * f.pullback, gofₓ)
  return gof
end

###############################################################################
#
# AbsVariety
#
mutable struct AbsVariety <: AbsVarietyT
  dim::Int
  ring::ChRing
  base::Ring
  point::ChRingElem
  O1::ChRingElem
  T::AbsSheaf
  bundles::Vector{AbsSheaf}
  struct_map::AbsVarietyHom
  @declare_other
  function AbsVariety(n::Int, R::ChRing)
    base = R.R.base_ring
    X = new(n, R, base)
    set_special(R, :variety => X)
    set_special(R, :variety_dim => n)
    return X
  end
end

# generic variety with some classes in given degrees
function variety(n::Int, symbols::Vector{String}, degs::Vector{Int}; base::Ring=Singular.QQ)
  @assert length(symbols) > 0
  R = ChRing(PolynomialRing(base, symbols)[1], degs)
  return AbsVariety(n, R), gens(R)
end

# generic variety with some bundles in given ranks
function variety(n::Int, bundles::Vector{Pair{Int,T}}; base::Ring=Singular.QQ) where T
  symbols = vcat([_parse_symbol(s,1:r) for (r,s) in bundles]...)
  degs = vcat([collect(1:r) for (r,s) in bundles]...)
  X = variety(n, symbols, degs, base=base)[1]
  i = 1
  X.bundles = AbsSheaf[]
  for (r,s) in bundles
    push!(X.bundles, AbsSheaf(X, r, 1 + sum(gens(X.ring)[i:i+r-1])))
    i += r
  end
  return X, X.bundles
end

# generic variety with tangent bundle
function variety(n::Int; base::Ring=Singular.QQ)
  n == 0 && return point()
  X, (T,) = variety(n, [n=>"c"], base=base)
  X.T = T
  return X
end

(X::AbsVariety)(f::Union{Scalar, RingElem}) = simplify(X.ring(f))

OO(X::AbsVariety) = AbsSheaf(X, X(1))
OO(X::AbsVariety, n::Scalar) = AbsSheaf(X, 1, 1+n*X.O1)
OO(X::AbsVariety, D::ChRingElem) = AbsSheaf(X, 1, 1+D[1])
degree(X::AbsVariety) = integral(X.O1^X.dim)
tangent_bundle(X::AbsVariety) = X.T
cotangent_bundle(X::AbsVariety) = dual(X.T)
canonical_class(X::AbsVariety) = -chern(1, X.T)
canonical_bundle(X::AbsVariety) = det(cotangent_bundle(X))
chern(X::AbsVariety) = chern(X.T)
chern(n::Int, X::AbsVariety) = chern(n, X.T)
euler(X::AbsVariety) = integral(chern(X.T))
todd(X::AbsVariety) = todd(X.T)
pontryagin(X::AbsVariety) = pontryagin(X.T)
pontryagin(n::Int, X::AbsVariety) = pontryagin(n, X.T)
chi(p::Int, X::AbsVariety) = chi(exterior_power(p, dual(X.T))) # generalized Todd genus

function todd_polynomial(n::Int)
  X = variety(n, base=QQ)
  R, z = X.ring.R["z"]
  sum(chi(p, X).f * (z-1)^p for p in 0:n)
end
function todd_polynomial(n::Int, k::Int)
  X = variety(n, base=QQ)
  R, (z,) = Nemo.PowerSeriesRing(X.ring.R, k+1, ["z"])
  sum(chi(p, X).f * (z-1)^p for p in 0:n)
end

chern_number(X::AbsVariety, λ::Int...) = chern_number(X, collect(λ))
chern_number(X::AbsVariety, λ::Partition) = chern_number(X, collect(λ))
function chern_number(X::AbsVariety, λ::Vector{Int})
  @assert sum(λ) == X.dim
  c = chern(X)[1:X.dim]
  integral(prod([c[i] for i in λ]))
end
function chern_numbers(X::AbsVariety)
  c = chern(X)[1:X.dim]
  [integral(prod([c[i] for i in λ])) for λ in partitions(X.dim)]
end

for g in [:a_hat_genus, :l_genus]
  @eval function $g(k::Int, X::AbsVariety)
    R = X.ring
    k == 0 && return R(1)
    p = pontryagin(X.T)[1:2k]
    R($g(k).f([p[2i].f for i in 1:k]...))
  end
  @eval function $g(X::AbsVariety)
    !iseven(X.dim) && error("the variety is not of even dimension")
    integral($g(X.dim÷2, X))
  end
end

signature(X::AbsVariety) = l_genus(X) # Hirzebruch signature theorem

function hilbert_polynomial(F::AbsSheaf)
  X, O1 = F.parent, F.parent.O1
  # first coerce the coefficient ring to QQ then extend to QQ(t)
  Qt, (t,) = FunctionField(Singular.QQ, ["t"])
  R = parent(Singular.change_base_ring(Qt, X.ring.R()))
  toQQ = x -> Singular.change_base_ring(Singular.QQ, x)
  toR = x -> Singular.change_base_ring(Qt, toQQ(x), parent=R)
  I = Ideal(R, toR.(gens(X.ring.I)))
  R_ = ChRing(R, X.ring.w, I, :variety_dim => X.dim)
  ch_O_t = 1 + _logg(1 + t * R_(toR(O1.f)))
  ch_F = R_(toR(F.ch.f))
  td = R_(toR(todd(X).f))
  pt = R_(toR(X.point.f))
  hilb = constant_coefficient(div(ch_F * ch_O_t * td, pt).f)
  # convert back to a true polynomial
  denom = Singular.n_transExt_to_spoly(denominator(hilb))
  denom = constant_coefficient(denom)
  return Singular.change_base_ring(QQ, 1//denom * Singular.n_transExt_to_spoly(hilb))
end
hilbert_polynomial(X::AbsVariety) = hilbert_polynomial(OO(X))

# find canonicallly defined morphisms from X to Y
function hom(X::AbsVariety, Y::AbsVariety)
  X == Y && return identity_hom(X)
  get_special(Y, :point) !== nothing && return hom(X, Y, [X(1)]) # Y is a point
  get_special(X, :point) !== nothing && return hom(X, Y, repeat([X(0)], length(gens(Y.ring)))) # X is a point
  # first handle the case where X is a (fibered) product
  projs = get_special(X, :projections)
  if projs !== nothing
    for p in projs
      p.codomain == Y && return p
    end
  else
    # follow the chain of structure maps to see if we can arrive at Y
    homs = AbsVarietyHom[]
    while isdefined(X, :struct_map) && X != Y
      push!(homs, X.struct_map)
      X = X.struct_map.codomain
    end
    X == Y && return reduce(*, homs)
  end
  error("no canonical homomorphism between the given varieties")
end
→(X::AbsVariety, Y::AbsVariety) = hom(X, Y)

# product variety
function *(X::AbsVariety, Y::AbsVariety)
  @assert X.base == Y.base
  base = X.base
  A, B = X.ring, Y.ring
  AI = isdefined(A, :I) ? A.I : Ideal(A.R, [A.R()])
  BI = isdefined(B, :I) ? B.I : Ideal(B.R, [B.R()])
  symsA, symsB = string.(gens(A.R)), string.(gens(B.R))
  a = length(symsA)
  R, x = PolynomialRing(base, vcat(symsA, symsB))
  IA = Ideal(R, [g(x[1:a]...) for g in gens(AI)])
  IB = Ideal(R, [g(x[a+1:end]...) for g in gens(BI)])
  AˣXY = ChRing(R, vcat(A.w, B.w), IA+IB)
  XY = AbsVariety(X.dim+Y.dim, AˣXY)
  if isdefined(X, :point) && isdefined(Y, :point)
    XY.point = XY(X.point.f(x[1:a]...) * Y.point.f(x[a+1:end]...))
  end
  p = AbsVarietyHom(XY, X, XY.(x[1:a]))
  q = AbsVarietyHom(XY, Y, XY.(x[a+1:end]))
  if isdefined(X, :T) && isdefined(Y, :T)
    XY.T = pullback(p, X.T) + pullback(q, Y.T)
  end
  if isdefined(X, :O1) && isdefined(Y, :O1) # Segre embedding
    XY.O1 = p.pullback(X.O1) + q.pullback(Y.O1)
  end
  set_special(XY, :projections => [p, q])
  return XY
end

###############################################################################
#
# Operators on AbsSheaf
#
function adams(k::Int, x::ChRingElem)
  R = x.parent
  n = get_special(R, :variety_dim)
  comps = x[0:n]
  sum([ZZ(k)^i*comps[i+1] for i in 0:n])
end

function dual(F::AbsSheaf)
  AbsSheaf(F.parent, adams(-1, F.ch))
end
+(n::Union{Scalar,RingElem}, F::AbsSheaf) = AbsSheaf(F.parent, n + F.ch)
*(n::Union{Scalar,RingElem}, F::AbsSheaf) = AbsSheaf(F.parent, n * F.ch)
+(F::AbsSheaf, n::Union{Scalar,RingElem}) = n + F
*(F::AbsSheaf, n::Union{Scalar,RingElem}) = n * F
-(F::AbsSheaf) = AbsSheaf(F.parent, -F.ch)
det(F::AbsSheaf) = AbsSheaf(F.parent, 1, 1 + F.ch[1])
function _coerce(F::AbsSheaf, G::AbsSheaf)
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

for O in [:(+), :(-), :(*)]
  @eval ($O)(F::AbsSheaf, G::AbsSheaf) = (
    (F, G) = _coerce(F, G);
    AbsSheaf(F.parent, $O(F.ch, G.ch)))
end
hom(F::AbsSheaf, G::AbsSheaf) = dual(F) * G

function exterior_power(k::Int, F::AbsSheaf)
  AbsSheaf(F.parent, _wedge(k, F.ch)[end])
end

function exterior_power(F::AbsSheaf)
  AbsSheaf(F.parent, sum([(-1)^(i-1) * w for (i, w) in enumerate(_wedge(F.rank, F.ch))]))
end

function symmetric_power(k::Int, F::AbsSheaf)
  AbsSheaf(F.parent, _sym(k, F.ch)[end])
end

function symmetric_power(k::Scalar, F::AbsSheaf)
  X = F.parent
  PF = proj(dual(F))
  p = PF.struct_map
  AbsSheaf(X, p.pushforward(sum((OO(PF, k).ch * todd(p))[0:PF.dim])))
end

function schur_functor(λ::Vector{Int}, F::AbsSheaf) schur_functor(Partition(λ), F) end
function schur_functor(λ::Partition, F::AbsSheaf)
  λ = conj(λ)
  X = F.parent
  w = _wedge(sum(λ), F.ch)
  S, ei = Nemo.PolynomialRing(QQ, ["e$i" for i in 1:length(w)])
  e = i -> (i < 0) ? S(0) : ei[i+1]
  M = [e(λ[i]-i+j) for i in 1:length(λ), j in 1:length(λ)]
  sch = det(Nemo.matrix(S, M)) # Jacobi-Trudi
  AbsSheaf(X, X(sch([wi.f for wi in w]...)))
end
function giambelli(λ::Vector{Int}, F::AbsSheaf)
  R = F.parent.ring
  M = [chern(λ[i]-i+j, F).f for i in 1:length(λ), j in 1:length(λ)]
  R(det(Nemo.matrix(R.R, M)))
end

###############################################################################
#
# Various computations
#
function basis(X::AbsVariety)
  !isdefined(X.ring, :I) && error("the ring has no ideal")
  Singular.dimension(X.ring.I) > 0 && error("the ideal is not 0-dimensional")
  X.ring.(gens(Singular.kbase(X.ring.I)))
end

function basis_by_degree(X::AbsVariety)
  n = X.dim
  b = basis(X)
  ans = [ChRingElem[] for i in 0:n]
  for bi in b
    push!(ans[total_degree(bi)+1], bi)
  end
  ans
end
basis(k::Int, X::AbsVariety) = basis_by_degree(X)[k+1]
betti(X::AbsVariety) = length.(basis_by_degree(X))

function integral(x::ChRingElem)
  X = get_special(parent(x), :variety)
  if isdefined(X, :point) && length(basis(X.dim, X)) == 1
    return (X.base==Singular.QQ ? QQ : X.base)(constant_coefficient(div(x, X.point).f))
  else
    return x[X.dim]
  end
end

function intersection_matrix(X::AbsVariety) intersection_matrix(basis(X)) end
function intersection_matrix(a::Vector{}, b=nothing)
  if b === nothing b = a end
  M = [integral(ai*bj) for ai in a, bj in b]
  try
    return Nemo.matrix(QQ, M)
  catch
    return M
  end
end

function dual_basis(X::AbsVariety)
  n = X.dim
  ans = Dict{RingElem, ChRingElem}()
  B = basis(X)
  # find dual using only classes in complementary dimensions
  Bd = basis_by_degree(X)
  for (i,b) in enumerate(Bd)
    l = length(b)
    comp = Bd[n+2-i]
    d = Matrix(inv(intersection_matrix(comp, b))) * comp
    for (j,bj) in enumerate(b)
      ans[bj.f] = d[j]
    end
  end
  [ans[B[i].f] for i in 1:length(B)]
end

function _expp(x::ChRingElem)
  R = x.parent
  n = get_special(R, :variety_dim)
  comps = x[0:n]
  p = [(-1)^i*factorial(ZZ(i))*comps[i+1] for i in 0:n]
  e = repeat([R(0)], n+1)
  e[1] = R(1)
  for i in 1:n
    e[i+1] = -1//ZZ(i) * sum(p[j+1] * e[i-j+1] for j in 1:i)
  end
  simplify(sum(e))
end

function _logg(x::ChRingElem)
  R = x.parent
  n = get_special(R, :variety_dim)
  p = repeat([R(0)], n+1)
  e = x[0:n]
  for i in 1:n
    p[i+1] = -ZZ(i)*e[i+1] - sum([e[j+1] * p[i-j+1] for j in 1:i-1], init=R(0))
  end
  simplify(sum([(-1)^i//factorial(ZZ(i))*p[i+1] for i in 1:n], init=R(0)))
end

function inv(x::ChRingElem)
  R = x.parent
  n = get_special(R, :variety_dim)
  S, t = Nemo.PowerSeriesRing(R.R, n+1, "t")
  comps = x[0:n]
  c = sum([t^i * comps[i+1].f for i in 0:n])
  s = inv(c)
  simplify(R(sum(Nemo.coeff(s, i) for i in 0:n)))
end

function Base.sqrt(x::ChRingElem)
  _expp(1//2*_logg(x))
end

# returns all the wedge from 0 to k
function _wedge(k::Int, x::ChRingElem)
  R = x.parent
  k == 0 && return [R(1)]
  n = get_special(R, :variety_dim)
  wedge = repeat([R(0)], k+1)
  wedge[1] = R(1)
  wedge[2] = x
  for j in 2:k
    wedge[j+1] = 1//ZZ(j) * sum(sum((-1)^(j-i+1) * wedge[i+1] * adams(j-i, x) for i in 0:j-1)[0:n])
  end
  wedge
end

# returns all the sym from 0 to k
function _sym(k::Int, x::ChRingElem)
  R = x.parent
  k == 0 && return [R(1)]
  n = get_special(R, :variety_dim)
  r = min(k, Int(Singular.ZZ(Singular.QQ(constant_coefficient(x.f)))))
  wedge = _wedge(r, x)
  sym = repeat([R(0)], k+1)
  sym[1] = R(1)
  sym[2] = x
  for j in 2:k
    sym[j+1] = sum(sum((-1)^(i+1) * wedge[i+1] * sym[j-i+1] for i in 1:min(j,r))[0:n])
  end
  sym
end

function _genus(x::ChRingElem, taylor::Vector{})
  R = x.parent
  x == 0 && return R(1)
  n = get_special(R, :variety_dim)
  R, (t,) = Nemo.PolynomialRing(QQ, ["t"])
  R_ = ChRing(R, [1], :variety_dim => n)
  lg = _logg(R_(sum(taylor[i+1] * t^i for i in 0:n)))
  comps = lg[1:n]
  lg = [leading_coefficient(comps[i].f) for i in 1:n]
  comps = x[1:n]
  _expp(sum(factorial(ZZ(i)) * lg[i] * comps[i] for i in 1:n))
end

function _todd(x::ChRingElem)
  n = get_special(parent(x), :variety_dim)
  # the Taylor series of t/(1-exp(-t))
  taylor = [(-1)^i//factorial(ZZ(i))*bernoulli(i) for i in 0:n]
  _genus(x, taylor)
end

function _l_genus(x::ChRingElem)
  n = get_special(parent(x), :variety_dim)
  # the Taylor series of sqrt(t)/tanh(sqrt(t))
  taylor = [ZZ(2)^2i//factorial(ZZ(2i))*bernoulli(2i) for i in 0:n]
  _genus(x, taylor)
end

function _a_hat_genus(x::ChRingElem)
  n = get_special(parent(x), :variety_dim)
  # the Taylor series of (sqrt(t)/2)/sinh(sqrt(t)/2)
  R, t = Nemo.PowerSeriesRing(QQ, 2n+1, "t")
  s = Nemo.divexact(t, exp(QQ(1//2)*t)-exp(-QQ(1//2)*t))
  taylor = [Nemo.coeff(s, 2i) for i in 0:n]
  _genus(x, taylor)
end

for (g,s) in [:a_hat_genus=>"p", :l_genus=>"p", :todd=>"c"]
  _g = Symbol("_", g)
  @eval function $g(n::Int)
    n == 0 && return QQ(1)
    R, p = Nemo.PolynomialRing(QQ, _parse_symbol($s, 1:n))
    R_ = ChRing(R, collect(1:n), :variety_dim => n)
    $_g(_logg(R_(1+sum(p))))[n]
  end
end

function section_zero_locus(F::AbsSheaf; class::Bool=false)
  X = F.parent
  R = X.ring
  cZ = ctop(F)
  # return only the class of Z in the chow ring of X
  class && return cZ
  I = Ideal(R.R, [cZ.f])
  I = Singular.quotient(isdefined(R, :I) ? R.I : Ideal(R.R, [R.R()]), I)
  AˣZ = ChRing(R.R, R.w, I)
  Z = AbsVariety(X.dim - F.rank, AˣZ)
  if isdefined(X, :point)
    ps = basis(Z.dim, Z) # the 0-cycles
    @assert length(ps) == 1 # make sure that the 0-cycle is unique
    p = ps[1]
    degp = integral(R(p.f) * cZ) # compute the degree of iₓp
    Z.point = Z(inv(degp) * p.f)
  end
  if isdefined(X, :T)
    Z.T = AbsSheaf(Z, Z((X.T.ch - F.ch).f))
  end
  if isdefined(X, :O1)
    Z.O1 = simplify(Z(X.O1.f))
  end
  iₓ = x -> simplify(x.f * cZ)
  iₓ = map_from_func(iₓ, Z.ring, X.ring)
  i = AbsVarietyHom(Z, X, Z.(gens(R.R)), iₓ)
  i.T = pullback(i, -F)
  Z.struct_map = i
  return Z
end

complete_intersection(P::AbsVariety, degs::Int...) = complete_intersection(P, collect(degs))
complete_intersection(P::AbsVariety, degs::Vector{Int}) = section_zero_locus(sum(OO(P, d) for d in degs))

function degeneracy_locus(k::Int, F::AbsSheaf, G::AbsSheaf; class::Bool=false)
  F, G = _coerce(F, G)
  m, n = rank(F), rank(G)
  @assert k < min(m,n)
  if class
    # return only the class of D in the chow ring of X
    if (m-k)*(n-k) <= F.parent.dim # Porteous' formula
      return _homog_comp((m-k)*(n-k), ch(schur_functor(repeat([m-k], n-k), G-F)))
    else # expected dimension is negative
      return F.parent.ring(0)
    end
  end
  Gr = (m-k == 1) ? proj(F) : flag(F, m-k, m)
  S = Gr.bundles[1]
  D = section_zero_locus(dual(S) * G)
  D.struct_map = D → F.parent # skip the flag variety
  return D
end

###############################################################################
#
# Projective spaces, Grassmannians, flag varieties
#
function point(; base::Ring=Singular.QQ)
  R, (p,) = PolynomialRing(base, ["p"])
  I = Ideal(R, [p])
  pt = AbsVariety(0, ChRing(R, [1], I))
  pt.point = pt(1)
  pt.T = AbsSheaf(pt, pt(0))
  pt.O1 = pt(0)
  set_special(pt, :description => "Point")
  set_special(pt, :point => true)
  return pt
end

function proj(n::Int; base::Ring=Singular.QQ, symbol::String="h")
  R, (h,) = PolynomialRing(base, [symbol])
  I = Ideal(R, [h^(n+1)])
  AˣP = ChRing(R, [1], I)
  P = AbsVariety(n, AˣP)
  P.point = P(h^n)
  P.O1 = P(h)
  chTP = R(n)
  for i in 1:n chTP += ZZ(n+1)//factorial(ZZ(i))*h^i end
  P.T = AbsSheaf(P, chTP)
  P.T.chern = P((1+h)^(n+1))
  S = AbsSheaf(P, 1, 1-h)
  Q = OO(P)*(n+1) - S
  P.bundles = [S, Q]
  P.struct_map = hom(P, point(base=base), [P(1)])
  set_special(P, :description => "Projective space of dim $n")
  set_special(P, :grassmannian => :absolute)
  set_special(P, :alg => true)
  return P
end

function proj(F::AbsSheaf; symbol::String="h")
  X, r = F.parent, F.rank
  !isa(r, Int) && error("expect rank to be an integer")
  R = X.ring
  syms = vcat([symbol], string.(gens(R.R)))
  # construct the ring
  R1, (h,) = PolynomialRing(X.base, syms)
  pback = x -> x(gens(R1)[2:end]...)
  pfwd = y -> y(vcat([R.R(0)], gens(R.R))...)
  # construct the ideal
  rels = [sum(pback(chern(i, F).f) * h^(r-i) for i in 0:r)]
  if isdefined(R, :I) rels = vcat(pback.(gens(R.I)), rels) end
  AˣPF = ChRing(R1, vcat([1], R.w), Ideal(R1, rels))
  # construct the variety
  PF = AbsVariety(X.dim+r-1, AˣPF)
  pₓ = x -> X(pfwd(div(x, PF(h^(r-1))).f))
  pₓ = map_from_func(pₓ, PF.ring, X.ring)
  p = AbsVarietyHom(PF, X, PF.(gens(R1)[2:end]), pₓ)
  if isdefined(X, :point) PF.point = p.pullback(X.point) * h^(r-1) end
  p.O1 = PF(h)
  PF.O1 = PF(h)
  S = AbsSheaf(PF, 1, 1-h)
  Q = pullback(p, F) - S
  p.T = dual(S)*Q
  if isdefined(X, :T) PF.T = pullback(p, X.T) + p.T end
  PF.bundles = [S, Q]
  PF.struct_map = p
  set_special(PF, :description => "Projectivization of $F")
  set_special(PF, :grassmannian => :relative)
  return PF
end

# combine the interface for AbsVariety and TnVariety versions
function grassmannian(k::Int, n::Int; bott::Bool=false, weights=:int, base::Ring=Singular.QQ, symbol::String="c")
  bott && return tn_grassmannian(k, n, weights=weights)
  abs_grassmannian(k, n, base=base, symbol=symbol)
end

function abs_grassmannian(k::Int, n::Int; base::Ring=Singular.QQ, symbol::String="c")
  @assert k < n
  d = k*(n-k)
  R, c = PolynomialRing(base, _parse_symbol(symbol, 1:k))
  AˣGr = ChRing(R, collect(1:k))
  cQ = sum((-sum(c))^i for i in 1:n) # this is c(Q) since c(S)⋅c(Q) = 1
  # Q is of rank n-k: the vanishing of Chern classes in higher degrees provides all the relations for the Chow ring
  AˣGr.I = std(Ideal(R, [x.f for x in AˣGr(cQ)[n-k+1:n]]))
  Gr = AbsVariety(d, AˣGr)
  Gr.O1 = Gr(-c[1])
  S = AbsSheaf(Gr, k, 1+sum(c))
  Q = OO(Gr)*n - S
  Gr.point = Gr((-1)^d*c[end]^(n-k))
  Gr.T = dual(S) * Q
  Gr.bundles = [S, Q]
  Gr.struct_map = hom(Gr, point(base=base), [Gr(1)])
  set_special(Gr, :description => "Grassmannian Gr($k, $n)")
  set_special(Gr, :grassmannian => :absolute)
  set_special(Gr, :alg => true)
  return Gr
end

# combine the interface for AbsVariety and TnVariety versions
function flag(dims::Int...; bott::Bool=false, weights=:int, base::Ring=Singular.QQ, symbol::String="c")
  bott && return tn_flag(collect(dims), weights=weights)
  abs_flag(collect(dims), base=base, symbol=symbol)
end

function flag(dims::Vector{Int}; bott::Bool=false, weights=:int, base::Ring=Singular.QQ, symbol::String="c")
  bott && return tn_flag(dims, weights=weights)
  abs_flag(dims, base=base, symbol=symbol)
end

function abs_flag(dims::Vector{Int}; base::Ring=Singular.QQ, symbol::String="c")
  n, l = dims[end], length(dims)
  ranks = pushfirst!([dims[i+1]-dims[i] for i in 1:l-1], dims[1])
  @assert all(r->r>0, ranks)
  d = sum(ranks[i] * sum(dims[end]-dims[i]) for i in 1:l-1)
  syms = vcat([_parse_symbol(symbol, i, 1:r) for (i,r) in enumerate(ranks)]...)
  R = PolynomialRing(base, syms)[1]
  AˣFl = ChRing(R, vcat([collect(1:r) for r in ranks]...))
  c = pushfirst!([1+sum(gens(R)[dims[i]+1:dims[i+1]]) for i in 1:l-1], 1+sum(gens(R)[1:dims[1]]))
  Rx, x = R["x"]
  gi = AˣFl(prod(c))[0:n]
  g = sum(gi[i+1].f * x^(n-i) for i in 0:n)
  rels = [Nemo.coeff(mod(x^n, g), i) for i in 0:n-1]
  AˣFl.I = std(Ideal(R, rels))
  Fl = AbsVariety(d, AˣFl)
  Fl.bundles = [AbsSheaf(Fl, r, ci) for (r,ci) in zip(ranks, c)]
  Fl.O1 = simplify(sum((i-1)*chern(1, Fl.bundles[i]) for i in 1:l))
  Fl.point = prod(ctop(E)^sum(dims[i]) for (i,E) in enumerate(Fl.bundles[2:end]))
  Fl.T = sum(dual(Fl.bundles[i]) * sum([Fl.bundles[j] for j in i+1:l]) for i in 1:l-1)
  Fl.struct_map = hom(Fl, point(base=base), [Fl(1)])
  set_special(Fl, :description => "Flag variety Flag$(tuple(dims...))")
  if l == 2 set_special(Fl, :grassmannian => :absolute) end
  set_special(Fl, :alg => true)
  return Fl
end

function flag(k::Int, F::AbsSheaf; symbol::String="c") flag([k], F, symbol=symbol) end
function flag(dims::Vector{Int}, F::AbsSheaf; symbol::String="c")
  X, n = F.parent, F.rank
  !isa(n, Int) && error("expect rank to be an integer")
  # compute the ranks and relative dim
  l = length(dims)
  ranks = pushfirst!([dims[i+1]-dims[i] for i in 1:l-1], dims[1])
  @assert all(r->r>0, ranks) && dims[end] <= n
  if dims[end] < n # the last dim can be omitted
    dims = vcat(dims, [n])
    push!(ranks, n-dims[l])
    l += 1
  end
  d = sum(ranks[i] * sum(dims[end]-dims[i]) for i in 1:l-1)
  # construct the ring
  R = X.ring
  syms = vcat([_parse_symbol(symbol, i, 1:r) for (i,r) in enumerate(ranks)]..., string.(gens(R.R)))
  R1 = PolynomialRing(X.base, syms)[1]
  pback = x -> x(gens(R1)[n+1:end]...)
  pfwd = y -> y(vcat(repeat([R.R(0)], n), gens(R.R)))
  AˣFl = ChRing(R1, vcat([collect(1:r) for r in ranks]..., R.w), :variety_dim => X.dim+d)
  # compute the relations
  c = pushfirst!([1+sum(gens(R1)[dims[i]+1:dims[i+1]]) for i in 1:l-1], 1+sum(gens(R1)[1:dims[1]]))
  Rx, x = R1["x"]
  fi = AˣFl(pback(chern(F).f))[0:n]
  f = sum(fi[i+1].f * x^(n-i) for i in 0:n)
  gi = AˣFl(prod(c))[0:n]
  g = sum(gi[i+1].f * x^(n-i) for i in 0:n)
  rels = [Nemo.coeff(mod(f, g), i) for i in 0:n-1]
  if isdefined(R, :I) rels = vcat(pback.(gens(R.I)), rels) end
  AˣFl.I = std(Ideal(R1, rels))
  Fl = AbsVariety(X.dim + d, AˣFl)
  Fl.bundles = [AbsSheaf(Fl, r, ci) for (r,ci) in zip(ranks, c)]
  section = prod(ctop(E)^sum(dims[i]) for (i, E) in enumerate(Fl.bundles[2:end]))
  pˣ = Fl.(gens(R1)[n+1:end])
  # TODO needs the block ordering to get the correct result
  # is there a workaround?
  pₓ = x -> (@warn "the result may be wrong"; X(pfwd(div(x, section).f)))
  pₓ = map_from_func(pₓ, Fl.ring, X.ring)
  p = AbsVarietyHom(Fl, X, pˣ, pₓ)
  if isdefined(X, :point)
    Fl.point = p.pullback(X.point) * section
  end
  p.O1 = simplify(sum((i-1)*chern(1, Fl.bundles[i]) for i in 1:l))
  Fl.O1 = p.O1
  p.T = sum(dual(Fl.bundles[i]) * sum([Fl.bundles[j] for j in i+1:l]) for i in 1:l-1)
  if isdefined(X, :T)
    Fl.T = pullback(p, X.T) + p.T
  end
  Fl.struct_map = p
  set_special(Fl, :description => "Relative flag variety Flag$(tuple(dims...)) for $F")
  set_special(Fl, :section => section)
  if l == 2 set_special(Fl, :grassmannian => :relative) end
  return Fl
end

function schubert_class(G::AbsVariety, λ::Int...) schubert_class(G, collect(λ)) end
function schubert_class(G::AbsVariety, λ::Partition) schubert_class(G, collect(λ)) end
function schubert_class(G::AbsVariety, λ::Vector{Int})
  get_special(G, :grassmannian) === nothing && error("the variety is not a Grassmannian")
  (length(λ) > rank(G.bundles[1]) || sort(λ, rev=true) != λ) && error("the Schubert input is not well-formed")
  giambelli(λ, G.bundles[2])
end
function schubert_classes(m::Int, G::AbsVariety)
  get_special(G, :grassmannian) === nothing && error("the variety is not a Grassmannian")
  S, Q = G.bundles
  [schubert_class(G, λ) for λ in partitions(m, rank(S), rank(Q))]
end
