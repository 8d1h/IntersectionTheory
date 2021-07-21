abstract type AbsVarietyT <: Variety end

###############################################################################
#
# AbsBundle
#
@doc Markdown.doc"""
    AbsBundle(X::AbsVariety, ch::ChRingElem)
    AbsBundle(X::AbsVariety, r, c::ChRingElem)
The type of an abstract bundle.
"""
mutable struct AbsBundle{V <: AbsVarietyT} <: Bundle
  parent::V
  rank::RingElement
  ch::ChRingElem
  chern::ChRingElem
  function AbsBundle(X::V, ch::RingElem) where V <: AbsVarietyT
    AbsBundle(X, X.ring(ch))
  end
  function AbsBundle(X::V, r::RingElement, c::RingElem) where V <: AbsVarietyT
    AbsBundle(X, r, X.ring(c))
  end
  function AbsBundle(X::V, ch::ChRingElem) where V <: AbsVarietyT
    ch = simplify(ch)
    r = constant_coefficient(ch.f)
    try r = Int(Singular.ZZ(Singular.QQ(r)))
    catch # r can contain symbolic variables
    end
    new{V}(X, r, ch)
  end
  function AbsBundle(X::V, r::RingElement, c::ChRingElem) where V <: AbsVarietyT
    F = new{V}(X, r)
    F.chern = c
    return F
  end
end
@doc Markdown.doc"""
    bundle(X::AbsVariety, ch)
    bundle(X::AbsVariety, r, c)
Construct a bundle on $X$ by specifying its Chern character, or its rank and
total Chern class.
"""
bundle(X::V, ch::RingElem) where V <: AbsVarietyT = AbsBundle(X, ch)
bundle(X::V, ch::ChRingElem) where V <: AbsVarietyT = AbsBundle(X, ch)
bundle(X::V, r::RingElement, c::RingElem) where V <: AbsVarietyT = AbsBundle(X, r, c)
bundle(X::V, r::RingElement, c::ChRingElem) where V <: AbsVarietyT = AbsBundle(X, r, c)

==(F::AbsBundle, G::AbsBundle) = ch(F) == ch(G)

@doc Markdown.doc"""
    ch(F::AbsBundle)
Return the Chern character."""
ch(F::AbsBundle) = (
  if !isdefined(F, :ch) F.ch = F.rank + _logg(F.chern) end;
  F.ch)

@doc Markdown.doc"""
    chern(F::AbsBundle)
    chern(F::TnBundle)
Compute the total Chern class.
"""
chern(F::AbsBundle) = (
  if !isdefined(F, :chern) F.chern = _expp(F.ch) end;
  F.chern)

@doc Markdown.doc"""
    chern(k::Int, F::AbsBundle)
    chern(k::Int, F::TnBundle)
Compute the $k$-th Chern class.
"""
chern(k::Int, F::AbsBundle) = (
  isdefined(F, :chern) && return chern(F)[k];
  _expp(F.ch, truncate=k)[k])

@doc Markdown.doc"""
    ctop(F::AbsBundle)
    ctop(F::TnBundle)
Compute the top Chern class.
"""
ctop(F::AbsBundle) = chern(F.rank, F)

@doc Markdown.doc"""
    segre(F::AbsBundle)
Compute the total Segre class."""
segre(F::AbsBundle) = chern(-F)

@doc Markdown.doc"""
    segre(k::Int, F::AbsBundle)
Compute the $k$-th Segre class."""
segre(k::Int, F::AbsBundle) = chern(k, -F)

@doc Markdown.doc"""
    todd(F::AbsBundle)
Compute the Todd class."""
todd(F::AbsBundle) = _todd(ch(F))

@doc Markdown.doc"""
    pontryagin(F::AbsBundle)
Compute the total Pontryagin class."""
function pontryagin(F::AbsBundle)
  n = F.parent.dim
  x = chern(F) * chern(dual(F))
  comps = x[0:n]
  sum([(-1)^i*comps[2i+1] for i in 0:n÷2])
end

@doc Markdown.doc"""
    pontryagin(k::Int, F::AbsBundle)
Compute the $k$-th Pontryagin class."""
pontryagin(k::Int, F::AbsBundle) = pontryagin(F)[2k]

@doc Markdown.doc"""
    chi(F::AbsBundle)
    chi(F::AbsBundle, G::AbsBundle)
Compute the holomorphic Euler characteristic $\chi(F)$, or the Euler pairing
$\chi(F,G)$.
"""
chi(F::AbsBundle) = integral(ch(F) * todd(F.parent)) # Hirzebruch-Riemann-Roch
chi(F::AbsBundle, G::AbsBundle) = begin
  F, G = _coerce(F, G)
  integral(ch(dual(F)) * ch(G) * todd(F.parent))
end

###############################################################################
#
# AbsVarietyHom
#
@doc Markdown.doc"""
    AbsVarietyHom(X::AbsVariety, Y::AbsVariety, fˣ::ChAlgHom, fₓ)
    AbsVarietyHom(X::AbsVariety, Y::AbsVariety, fˣ::Vector, fₓ)
The type of an abstract variety morphism.
"""
mutable struct AbsVarietyHom{V1 <: AbsVarietyT, V2 <: AbsVarietyT} <: VarietyHom
  domain::V1
  codomain::V2
  dim::Int
  pullback::ChAlgHom
  pushforward::FunctionalMap
  O1::ChRingElem
  T::AbsBundle{V1}
  function AbsVarietyHom(X::V1, Y::V2, fˣ::ChAlgHom, fₓ=nothing) where {V1 <: AbsVarietyT, V2 <: AbsVarietyT}
    if !(fₓ isa FunctionalMap) && isdefined(X, :point) && isdefined(Y, :point)
      # pushforward can be deduced from pullback in the following cases
      # - explicitly specified (f is relatively algebraic)
      # - X is a point
      # - Y is a point or a curve
      # - all algebraic classes for Y are known
      f_is_alg = fₓ == :alg || dim(X) == 0 || dim(Y) ≤ 1 || get_special(Y, :alg) == true
      fₓ = x -> (
	if !f_is_alg
	  @warn "assuming that all algebraic classes are known for\n$Y\notherwise the result may be wrong"
	end;
	sum(integral(xi*fˣ(yi))*di for (i, xi) in zip(dim(Y):-1:0, x[dim(X)-dim(Y):dim(X)])
	    if xi !=0 for (yi, di) in zip(basis(i, Y), dual_basis(i, Y))))
      fₓ = map_from_func(fₓ, X.ring, Y.ring)
    end
    f = new{V1, V2}(X, Y, X.dim-Y.dim, fˣ)
    try
      f.pushforward = fₓ
    catch
    end
    if isdefined(X, :T) && isdefined(Y, :T)
      f.T = AbsBundle(X, ch(X.T) - fˣ(ch(Y.T)))
    end
    return f
  end
  function AbsVarietyHom(X::V1, Y::V2, l::Vector, fₓ=nothing) where {V1 <: AbsVarietyT, V2 <: AbsVarietyT}
    fˣ = ChAlgHom(Y.ring, X.ring, l)
    AbsVarietyHom(X, Y, fˣ, fₓ)
  end
end

@doc Markdown.doc"""
    dim(f::AbsVarietyHom)
Return the relative dimension."""
dim(f::AbsVarietyHom) = f.dim

@doc Markdown.doc"""
    tangent_bundle(f::AbsVarietyHom)
Return the relative tangent bundle."""
tangent_bundle(f::AbsVarietyHom) = f.T

@doc Markdown.doc"""
    cotangent_bundle(f::AbsVarietyHom)
Return the relative cotangent bundle."""
cotangent_bundle(f::AbsVarietyHom) = dual(f.T)

@doc Markdown.doc"""
    todd(f::AbsVarietyHom)
Compute the Todd class of the relative tangent bundle."""
todd(f::AbsVarietyHom) = todd(f.T)

@doc Markdown.doc"""
    pullback(f::AbsVarietyHom, x::ChRingElem)
    pullback(f::AbsVarietyHom, F::AbsBundle)
Compute the pullback of a Chow ring element $x$ or a bundle $F$ by a morphism $f$.
"""
pullback(f::AbsVarietyHom, x::ChRingElem) = f.pullback(x)
pullback(f::AbsVarietyHom, F::AbsBundle) = AbsBundle(f.domain, f.pullback(ch(F)))

@doc Markdown.doc"""
    pushforward(f::AbsVarietyHom, x::ChRingElem)
    pushforward(f::AbsVarietyHom, F::AbsBundle)
Compute the pushforward of a Chow ring element $x$ or a bundle $F$ by a
morphism $f$. For abstract bundles, the pushforward is derived, e.g., for a
bundle $F$ it is understood as the alternating sum of all direct images.
"""
pushforward(f::AbsVarietyHom, x::ChRingElem) = f.pushforward(x)
pushforward(f::AbsVarietyHom, F::AbsBundle) = AbsBundle(f.codomain, f.pushforward(ch(F) * todd(f))) # Grothendieck-Hirzebruch-Riemann-Roch

function identity_hom(X::V) where V <: AbsVarietyT
  AbsVarietyHom(X, X, gens(X.ring), map_from_func(identity, X.ring, X.ring))
end

@doc Markdown.doc"""
    *(f::AbsVarietyHom, g::AbsVarietyHom)
Construct the composition morphism $g\circ f: X\to Z$ for $f: X\to Y$ and $g:Y\to Z$.
"""
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
@doc Markdown.doc"""
    AbsVariety(n::Int, R::ChRing)
The type of an abstract variety."""
mutable struct AbsVariety <: AbsVarietyT
  dim::Int
  ring::ChRing
  base::Ring
  point::ChRingElem
  O1::ChRingElem
  T::AbsBundle
  bundles::Vector{AbsBundle}
  struct_map::AbsVarietyHom
  @declare_other
  function AbsVariety(n::Int, R::ChRing)
    base = base_ring(R)
    X = new(n, R, base)
    set_special(R, :variety => X)
    set_special(R, :variety_dim => n)
    return X
  end
end

trim!(X::AbsVariety) = (trim!(X.ring); X)

variety(n::Int, R::ChRing) = AbsVariety(n, R)

@doc Markdown.doc"""
    hom(X::AbsVariety, Y::AbsVariety, fˣ::Vector)
    hom(X::AbsVariety, Y::AbsVariety, fˣ::Vector, fₓ)

Construct a variety morphism from $X$ to $Y$, by specifying the pullbacks of
the generators of the Chow ring of $Y$. The pushforward can be automatically
computed in certain cases.

In case of an inclusion $i:X\hookrightarrow Y$ where the class of $X$ is not
present in the Chow ring of $Y$, use the argument `inclusion=true`.
A copy of $Y$ will be created, with extra classes added so that one can
pushforward classes on $X$.
"""
function hom(X::AbsVariety, Y::AbsVariety, fˣ::Vector, fₓ=nothing; inclusion::Bool=false, symbol::String="x")
  !inclusion && return AbsVarietyHom(X, Y, fˣ, fₓ)
  _inclusion(AbsVarietyHom(X, Y, fˣ), symbol=symbol)
end

# generic variety with some classes in given degrees
@doc Markdown.doc"""
    variety(n::Int, symbols::Vector{String}, degs::Vector{Int})

Construct a generic variety of dimension $n$ with some classes in given degrees.

Return the variety and the list of classes.
"""
function variety(n::Int, symbols::Vector{String}, degs::Vector{Int}; base::Ring=QQ, param::Union{String, Vector{String}}=String[])
  base, param = _parse_base(base, param)
  @assert length(symbols) > 0
  R = ChRing(PolynomialRing(base, symbols)[1], degs)
  X = AbsVariety(n, R)
  return param == [] ? (X, gens(R)) : (X, gens(R), param)
end

# generic variety with some bundles in given ranks
@doc Markdown.doc"""
    variety(n::Int, bundles::Vector{Pair{Int, T}}) where T

Construct a generic variety of dimension $n$ with some bundles of given ranks.

Return the variety and the list of bundles.
"""
function variety(n::Int, bundles::Vector{Pair{Int, T}}; base::Ring=QQ, param::Union{String, Vector{String}}=String[]) where T
  symbols = vcat([_parse_symbol(s,1:r) for (r,s) in bundles]...)
  degs = vcat([collect(1:r) for (r,s) in bundles]...)
  ans = variety(n, symbols, degs, base=base, param=param)
  X = ans[1]
  param = length(ans) == 3 ? ans[3] : []
  i = 1
  X.bundles = AbsBundle[]
  for (r,s) in bundles
    push!(X.bundles, AbsBundle(X, r, 1 + sum(gens(X.ring)[i:i+r-1])))
    i += r
  end
  return param == [] ? (X, X.bundles) : (X, X.bundles, param)
end

# generic variety with tangent bundle
@doc Markdown.doc"""
    variety(n::Int)

Construct a generic variety of dimension $n$ and define its tangent bundle.

Return the variety.
"""
function variety(n::Int; base::Ring=QQ, param::Union{String, Vector{String}}=String[])
  n == 0 && return point(base=base, param=param)
  ans = variety(n, [n=>"c"], base=base, param=param)
  X, (T,) = ans[1], ans[2]
  param = length(ans) == 3 ? ans[3] : []
  X.T = T
  return param == [] ? X : (X, param)
end

@doc Markdown.doc"""
    curve(g)
Construct a curve of genus $g$. The genus can either be an integer or a string
to allow symbolic computations."""
function curve(g::Union{Int, String}; base::Ring=QQ, param::Union{String, Vector{String}}=String[])
  if g isa String
    C, (p,), gp = variety(1, ["p"], [1], base=base, param=vcat([g], param))
    g, param = gp[1], param isa String ? gp[2] : gp[2:end]
  else
    ans = variety(1, ["p"], [1], base=base, param=param)
    C, (p,) = ans[1], ans[2]
    param = length(ans) == 3 ? ans[3] : []
  end
  trim!(C)
  C.point = p
  C.T = bundle(C, 1 + (2-2g)p)
  return param == [] ? C : (C, param)
end

(X::AbsVariety)(f::RingElement) = X.ring(f, reduce=true)
gens(X::AbsVariety) = gens(X.ring)
base_ring(X::AbsVariety) = X.base

@doc Markdown.doc"""
    OO(X::AbsVariety)
    OO(X::TnVariety)
Return the trivial bundle $\mathcal O_X$ on $X$.
"""
OO(X::AbsVariety) = AbsBundle(X, X(1))
@doc Markdown.doc"""
    OO(X::AbsVariety, n)
    OO(X::AbsVariety, D)
Return the line bundle $\mathcal O_X(n)$ on $X$ if $X$ has been given a
polarization, or a line bundle $\mathcal O_X(D)$ with first Chern class $D$.
"""
OO(X::AbsVariety, n::RingElement) = AbsBundle(X, 1, 1 + X.base(n)*X.O1)
OO(X::AbsVariety, D::ChRingElem) = AbsBundle(X, 1, 1 + D[1])

@doc Markdown.doc"""
    degree(X::AbsVariety)
Compute the degree of $X$ with respect to its polarization."""
degree(X::AbsVariety) = integral(X.O1^X.dim)

@doc Markdown.doc"""
    tangent_bundle(X::AbsVariety)
    tangent_bundle(X::TnVariety)
Return the tangent bundle of a variety $X$. Same as `X.T`.
"""
tangent_bundle(X::AbsVariety) = X.T

@doc Markdown.doc"""
    cotangent_bundle(X::AbsVariety)
    cotangent_bundle(X::TnVariety)
Return the cotangent bundle of a variety $X$.
"""
cotangent_bundle(X::AbsVariety) = dual(X.T)

@doc Markdown.doc"""
    canonical_class(X::AbsVariety)
Return the canonical class of a variety $X$."""
canonical_class(X::AbsVariety) = -chern(1, X.T)

@doc Markdown.doc"""
    canonical_bundle(X::AbsVariety)
Return the canonical bundle of a variety $X$."""
canonical_bundle(X::AbsVariety) = det(cotangent_bundle(X))

@doc Markdown.doc"""
    bundles(X::AbsVariety)
    bundles(X::TnVariety)
Return the tautological bundles of a variety $X$. Same as `X.bundles`.
"""
bundles(X::AbsVariety) = X.bundles

@doc Markdown.doc"""
    chern(X::AbsVariety)
    chern(X::TnVariety)
Compute the total Chern class of the tangent bundle of $X$.
"""
chern(X::AbsVariety) = chern(X.T)

@doc Markdown.doc"""
    chern(k::Int, X::AbsVariety)
    chern(k::Int, X::TnVariety)
Compute the $k$-th Chern class of the tangent bundle of $X$.
"""
chern(k::Int, X::AbsVariety) = chern(k, X.T)

@doc Markdown.doc"""
    euler(X::AbsVariety)
    euler(X::TnVariety)
Compute the Euler number of a variety $X$.
"""
euler(X::AbsVariety) = integral(chern(X.T))

@doc Markdown.doc"""
    todd(X::AbsVariety)
    todd(X::TnVariety)
Compute the Todd class of the tangent bundle of $X$."""
todd(X::AbsVariety) = todd(X.T)

@doc Markdown.doc"""
    pontryagin(X::AbsVariety)
Compute the total Pontryagin class of the tangent bundle of $X$."""
pontryagin(X::AbsVariety) = pontryagin(X.T)

@doc Markdown.doc"""
    pontryagin(k::Int, X::AbsVariety)
Compute the $k$-th Pontryagin class of the tangent bundle of $X$."""
pontryagin(k::Int, X::AbsVariety) = pontryagin(k, X.T)

chi(p::Int, X::AbsVariety) = chi(exterior_power(p, dual(X.T))) # generalized Todd genus

# introduced by Libgober-Wood
# see https://arxiv.org/abs/1512.04321
@doc Markdown.doc"""
    libgober_wood_polynomial(n::Int)
    libgober_wood_polynomial(X::AbsVariety)
Compute the polynomial defined by Libgober--Wood in dimension $n$.
"""
function libgober_wood_polynomial(X::AbsVariety)
  F = parent(integral(X(0)))
  R, z = Nemo.PolynomialRing(F, "z")
  sum([chi(p, X) * (z-1)^p for p in 0:dim(X)])
end
libgober_wood_polynomial(n::Int) = libgober_wood_polynomial(variety(n))

@doc Markdown.doc"""
    chern_number(X::Variety, λ::Int...)
    chern_number(X::Variety, λ::Vector{Int})
    chern_number(X::Variety, λ::Partition)
Compute the Chern number $c_\lambda (X):=\int_X c_{\lambda_1}(X)\cdots
c_{\lambda_k}(X)$, where $\lambda:=(\lambda_1,\dots,\lambda_k)$ is a partition
of the dimension of $X$.
"""
chern_number(X::Variety, λ::Int...) = chern_number(X, collect(λ))
chern_number(X::Variety, λ::Partition) = chern_number(X, collect(λ))
function chern_number(X::AbsVariety, λ::Vector{Int})
  sum(λ) == dim(X) || error("not a partition of the dimension")
  c = chern(X)[1:dim(X)]
  integral(prod([c[i] for i in λ]))
end

@doc Markdown.doc"""
    chern_numbers(X::Variety)
    chern_numbers(X::Variety, P::Vector{<:Partition})
Compute all the Chern numbers of $X$ as a dictionary of $\lambda\Rightarrow
c_\lambda(X)$, or only those corresponding to partitions in a given vector.
"""
chern_numbers(X::Variety)

function chern_numbers(X::AbsVariety, P::Vector{<:Partition}=partitions(dim(X)))
  all(λ -> sum(λ) == dim(X), P) || error("not a partition of the dimension")
  c = chern(X)[1:dim(X)]
  Dict([λ => integral(prod([c[i] for i in λ])) for λ in P])
end

for g in [:a_hat_genus, :l_genus]
  @eval function $g(k::Int, X::AbsVariety)
    R = X.ring
    k == 0 && return R(1)
    p = pontryagin(X.T)[1:2k]
    R($g(k)[k].f([p[2i].f for i in 1:k]...))
  end
end

@doc Markdown.doc"""
    a_hat_genus(k::Int, X::AbsVariety)
Compute the $k$-th $\hat A$ genus of a variety $X$."""
a_hat_genus(k::Int, X::AbsVariety)

@doc Markdown.doc"""
    l_genus(k::Int, X::AbsVariety)
Compute the $k$-th L genus of a variety $X$."""
l_genus(k::Int, X::AbsVariety)

@doc Markdown.doc"""
    a_hat_genus(X::AbsVariety)
Compute the $\hat A$ genus of a variety $X$."""
function a_hat_genus(X::AbsVariety)
  integral(todd(X) * _expp(-1//2 * chern(1, X)))
end

@doc Markdown.doc"""
    signature(X::AbsVariety)
Compute the signature of a variety $X$."""
function signature(X::AbsVariety)
  iseven(dim(X)) || return integral(X(0))
  integral(l_genus(dim(X)÷2, X)) # Hirzebruch signature theorem
end

@doc Markdown.doc"""
    hilbert_polynomial(F::AbsBundle)
    hilbert_polynomial(X::AbsVariety)
Compute the Hilbert polynomial of a bundle $F$ or the Hilbert polynomial of $X$
itself, with respect to the polarization $\mathcal O_X(1)$ on $X$.
"""
function hilbert_polynomial(F::AbsBundle)
  !isdefined(F.parent, :O1) && error("no polarization is specified for the variety")
  X, O1 = F.parent, F.parent.O1
  # extend the coefficient ring to QQ(t)
  Qt, (t,) = PolynomialRing(X.base, ["t"])
  Qt = Nemo.FractionField(Qt)
  sQt = Singular.CoefficientRing(Qt)
  toR = x -> Singular.change_base_ring(sQt, x)
  R = parent(toR(X.ring.R()))
  I = Ideal(R, toR.(gens(X.ring.I)))
  R_ = ChRing(R, X.ring.w, I, :variety_dim => X.dim)
  ch_O_t = 1 + _logg(1 + sQt(t) * R_(toR(O1.f)))
  ch_F = R_(toR(ch(F).f))
  td = R_(toR(todd(X).f))
  pt = R_(toR(X.point.f))
  hilb = Qt(constant_coefficient(div(ch_F * ch_O_t * td, pt).f))
  # convert back to a true polynomial
  denom = constant_coefficient(denominator(hilb))
  return 1//denom * numerator(hilb)
end
hilbert_polynomial(X::AbsVariety) = hilbert_polynomial(OO(X))

# find canonically defined morphism from X to Y
function _hom(X::AbsVariety, Y::AbsVariety)
  X == Y && return identity_hom(X)
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

# morphisms for points are convenient, but are not desired when doing coercion
@doc Markdown.doc"""
    hom(X::AbsVariety, Y::AbsVariety)
Return a canonically defined morphism from $X$ to $Y$."""
function hom(X::AbsVariety, Y::AbsVariety)
  get_special(Y, :point) !== nothing && return hom(X, Y, [X(0)]) # Y is a point
  get_special(X, :point) !== nothing && return hom(X, Y, repeat([X(0)], length(gens(Y.ring)))) # X is a point
  _hom(X, Y)
end
→(X::AbsVariety, Y::AbsVariety) = hom(X, Y)

# product variety
@doc Markdown.doc"""
    *(X::AbsVariety, Y::AbsVariety)
Construct the product variety $X\times Y$. If both $X$ and $Y$ have a
polarization, $X\times Y$ will be endowed with the polarization of the Segre
embedding.
"""
function *(X::AbsVariety, Y::AbsVariety)
  prod_cache = get_special(X, :prod_cache)
  prod_cache !== nothing && Y in keys(prod_cache) && return prod_cache[Y]
  if prod_cache === nothing
    prod_cache = Dict{AbsVariety, AbsVariety}()
    set_special(X, :prod_cache => prod_cache)
  end
  @assert X.base == Y.base
  base = X.base
  A, B = X.ring, Y.ring
  symsA, symsB = string.(gens(A.R)), string.(gens(B.R))
  a = length(symsA)
  R, x = PolynomialRing(base, vcat(symsA, symsB))
  AtoR = Singular.AlgebraHomomorphism(A.R, R, x[1:a])
  BtoR = Singular.AlgebraHomomorphism(B.R, R, x[a+1:end])
  IA = Ideal(R, isdefined(A, :I) ? AtoR.(gens(A.I)) : [R()])
  IB = Ideal(R, isdefined(B, :I) ? BtoR.(gens(B.I)) : [R()])
  AˣXY = ChRing(R, vcat(A.w, B.w), IA+IB)
  XY = AbsVariety(X.dim+Y.dim, AˣXY)
  if isdefined(X, :point) && isdefined(Y, :point)
    XY.point = XY(AtoR(X.point.f) * BtoR(Y.point.f))
  end
  p = AbsVarietyHom(XY, X, XY.(x[1:a]))
  q = AbsVarietyHom(XY, Y, XY.(x[a+1:end]))
  if isdefined(X, :T) && isdefined(Y, :T)
    XY.T = pullback(p, X.T) + pullback(q, Y.T)
    XY.T.chern = pullback(p, chern(X.T)) * pullback(q, chern(Y.T))
  end
  if isdefined(X, :O1) && isdefined(Y, :O1) # Segre embedding
    XY.O1 = p.pullback(X.O1) + q.pullback(Y.O1)
  end
  if get_special(X, :alg) == true && get_special(Y, :alg) == true
    set_special(XY, :alg => true)
  end
  set_special(XY, :projections => [p, q])
  set_special(XY, :description => "Product of $X and $Y")
  prod_cache[Y] = XY
  return XY
end

@doc Markdown.doc"""
    graph(f::AbsVarietyHom)
Given a morphism $f: X\to Y$, construct $i:\Gamma_f\to X\times Y$, the
inclusion of the graph into the product.
"""
function graph(f::AbsVarietyHom)
  X, Y = f.domain, f.codomain
  hom(X, X * Y, vcat(gens(X), f.pullback.image))
end

###############################################################################
#
# Operators on AbsBundle
#
function adams(k::Int, x::ChRingElem)
  R = x.parent
  n = get_special(R, :variety_dim)
  comps = x[0:n]
  sum([ZZ(k)^i*comps[i+1] for i in 0:n])
end

@doc Markdown.doc"""
    dual(F::AbsBundle)
    dual(F::TnBundle)
Return the dual bundle.
"""
function dual(F::AbsBundle)
  Fdual = AbsBundle(F.parent, adams(-1, ch(F)))
  if isdefined(F, :chern)
    Fdual.chern = adams(-1, chern(F))
  end
  return Fdual
end
+(n::RingElement, F::AbsBundle) = AbsBundle(F.parent, n + ch(F))
*(n::RingElement, F::AbsBundle) = AbsBundle(F.parent, n * ch(F))
+(F::AbsBundle, n::RingElement) = n + F
*(F::AbsBundle, n::RingElement) = n * F
-(F::AbsBundle) = AbsBundle(F.parent, -ch(F))
^(F::AbsBundle, n::Int) = AbsBundle(F.parent, ch(F)^n)

@doc Markdown.doc"""
    det(F::AbsBundle)
    det(F::TnBundle)
Return the determinant bundle.
"""
det(F::AbsBundle) = AbsBundle(F.parent, 1, 1 + chern(1, F))
function _coerce(F::AbsBundle, G::AbsBundle)
  X, Y = F.parent, G.parent
  X == Y && return F, G
  try
    return F, pullback(_hom(X, Y), G)
  catch
    try
      return pullback(_hom(Y, X), F), G
    catch
      error("the sheaves are not on compatible varieties")
    end
  end
end

for O in [:(+), :(-), :(*)]
  @eval ($O)(F::AbsBundle, G::AbsBundle) = (
    (F, G) = _coerce(F, G);
    AbsBundle(F.parent, $O(ch(F), ch(G))))
end
hom(F::AbsBundle, G::AbsBundle) = dual(F) * G

@doc Markdown.doc"""
    exterior_power(k::Int, F::AbsBundle)
    exterior_power(k::Int, F::TnBundle)
Return the $k$-th exterior power.
"""
function exterior_power(k::Int, F::AbsBundle)
  AbsBundle(F.parent, _wedge(k, ch(F))[end])
end

function exterior_power(F::AbsBundle)
  AbsBundle(F.parent, sum([(-1)^(i-1) * w for (i, w) in enumerate(_wedge(F.rank, ch(F)))]))
end

@doc Markdown.doc"""
    symmetric_power(k, F::AbsBundle)
    symmetric_power(k::Int, F::TnBundle)
Return the $k$-th symmetric power. For an `AbsBundle`, $k$ can contain parameters.
"""
function symmetric_power(k::Int, F::AbsBundle)
  AbsBundle(F.parent, _sym(k, ch(F))[end])
end

function symmetric_power(k::RingElement, F::AbsBundle)
  X = F.parent
  PF = proj(dual(F))
  p = PF.struct_map
  AbsBundle(X, p.pushforward(sum((ch(OO(PF, k)) * todd(p))[0:PF.dim])))
end

@doc Markdown.doc"""
    schur_functor(λ::Vector{Int}, F::AbsBundle)
    schur_functor(λ::Partition, F::AbsBundle)
Return the result of the Schur functor $\mathbf S^\lambda$.
"""
function schur_functor(λ::Vector{Int}, F::AbsBundle) schur_functor(Partition(λ), F) end
function schur_functor(λ::Partition, F::AbsBundle)
  λ = conj(λ)
  X = F.parent
  w = _wedge(sum(λ), ch(F))
  S, ei = PolynomialRing(Singular.QQ, ["e$i" for i in 1:length(w)])
  e = i -> (i < 0) ? S(0) : ei[i+1]
  M = [e(λ[i]-i+j) for i in 1:length(λ), j in 1:length(λ)]
  sch = det(Nemo.matrix(S, M)) # Jacobi-Trudi
  StoX = Singular.AlgebraHomomorphism(S, X.ring.R, [wi.f for wi in w])
  AbsBundle(X, X(StoX(sch)))
end
function giambelli(λ::Vector{Int}, F::AbsBundle)
  R = F.parent.ring
  M = [chern(λ[i]-i+j, F).f for i in 1:length(λ), j in 1:length(λ)]
  R(det(Nemo.matrix(R.R, M)))
end

###############################################################################
#
# Various computations
#
@doc Markdown.doc"""
    basis(X::AbsVariety)
Return an additive basis of the Chow ring of $X$, grouped by increasing
degree (i.e., increasing codimension)."""
function basis(X::AbsVariety)
  # it is important for this to be cached!
  if get_special(X, :basis) === nothing
    try_trim = "Try use `trim!`."
    isdefined(X.ring, :I) || error("the ring has no ideal. "*try_trim)
    Singular.dimension(X.ring.I) > 0 && error("the ideal is not 0-dimensional. "*try_trim)
    b = X.ring.(gens(Singular.kbase(X.ring.I)))
    ans = [ChRingElem[] for i in 0:X.dim]
    for bi in b
      push!(ans[total_degree(bi)+1], bi)
    end
    set_special(X, :basis => ans)
  end
  return get_special(X, :basis)
end

@doc Markdown.doc"""
    basis(k::Int, X::AbsVariety)
Return an additive basis of the Chow ring of $X$ in codimension $k$."""
basis(k::Int, X::AbsVariety) = basis(X)[k+1]

@doc Markdown.doc"""
    betti(X::AbsVariety)
Return the Betti numbers of the Chow ring of $X$. Note that these are not
necessarily equal to the usual Betti numbers, i.e., the dimensions of
(co)homologies."""
betti(X::AbsVariety) = length.(basis(X))

@doc Markdown.doc"""
    integral(x::ChRingElem)

Compute the integral of a Chow ring element.

If the variety $X$ has a (unique) point class `X.point`, the integral will be a
number (an `fmpq` or a function field element). Otherwise the 0-dimensional
part of $x$ is returned.
"""
function integral(x::ChRingElem)
  X = get_special(parent(x), :variety)
  if isdefined(X, :point) && length(basis(X.dim, X)) == 1
    return (X.base==Singular.QQ ? QQ : X.base)(constant_coefficient(div(x, X.point).f))
  else
    return x[X.dim]
  end
end

@doc Markdown.doc"""
    intersection_matrix(a::Vector)
    intersection_matrix(a::Vector, b::Vector)
    intersection_matrix(X::AbsVariety)

Compute the intersection matrix among entries of a vector $a$ of Chow ring
elements, or between two vectors $a$ and $b$. For a variety $X$, this computes
the intersection matrix of the additive basis given by `basis(X)`.
"""
function intersection_matrix(X::AbsVariety) intersection_matrix(vcat(basis(X)...)) end
function intersection_matrix(a::Vector{}, b=nothing)
  if b === nothing b = a end
  M = [integral(ai*bj) for ai in a, bj in b]
  try
    return Nemo.matrix(QQ, M)
  catch
    return Nemo.matrix(parent(M[1, 1]), M)
  end
end

@doc Markdown.doc"""
    dual_basis(k::Int, X::AbsVariety)
Compute the dual basis of the additive basis in codimension $k$ given by
`basis(k, X)` (the returned elements are therefore in codimension
$\dim X-k$)."""
function dual_basis(k::Int, X::AbsVariety)
  d = get_special(X, :dual_basis)
  if d === nothing
    d = Dict{Int, Vector{ChRingElem}}()
    set_special(X, :dual_basis => d)
  end
  if !(k in keys(d))
    B = basis(X)
    b_k = B[k+1]
    b_comp = B[X.dim-k+1]
    M = Matrix(inv(intersection_matrix(b_comp, b_k)))
    d[k] = M * b_comp
    d[X.dim-k] = M' * b_k
  end
  return d[k]
end

@doc Markdown.doc"""
    dual_basis(X::AbsVariety)
Compute the dual basis with respect to the additive basis given by `basis(X)`,
grouped by decreasing degree (i.e., decreasing codimension)."""
dual_basis(X::AbsVariety) = [dual_basis(k, X) for k in 0:X.dim]

# the parameter for truncation is usually the dimension, but can also be set
# manually, which is used when computing particular Chern classes (without
# computing the total Chern class)
function _expp(x::ChRingElem; truncate::Int=-1)
  R = x.parent
  n = truncate < 0 ? get_special(R, :variety_dim) : truncate
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
  n == 0 && return R()
  e = x[1:n]
  p = pushfirst!(repeat([R()], n-1), -e[1])
  for i in 1:n-1
    p[i+1] = -ZZ(i+1)*e[i+1] - sum(e[j] * p[i-j+1] for j in 1:i)
  end
  simplify(sum((-1)^i//factorial(ZZ(i))*p[i] for i in 1:n))
end

function inv(x::ChRingElem)
  R = x.parent
  n = get_special(R, :variety_dim)
  S, t = Nemo.PowerSeriesRing(R.R, n+1, "t")
  comps = x[0:n]
  c = sum([t^i * comps[i+1].f for i in 0:n])
  s = inv(c)
  R(sum(Nemo.coeff(s, i) for i in 0:n), reduce=true)
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

function _genus(x::ChRingElem, taylor::Vector{T}; twist::U=0) where {T <: RingElement, U <: RingElement}
  R = x.parent
  x == 0 && return R(1)
  n = get_special(R, :variety_dim)
  S, (t,) = Nemo.PolynomialRing(parent(taylor[1]), ["t"])
  S = ChRing(S, [1], :variety_dim => n)
  lg = _logg(S(sum(taylor[i+1] * t^i for i in 0:n)))
  lg = [coeff(lg, [i]) for i in 1:n]
  comps = x[1:n]
  _expp(sum(factorial(ZZ(i)) * lg[i] * comps[i] for i in 1:n) + twist * gens(R)[1])
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
    $_g(_logg(R_(1+sum(p))))
  end
end

@doc Markdown.doc"""
    todd(n::Int)
Compute the total class of the Todd genus up to degree $n$, in terms of the
Chern classes."""
todd(n::Int)

@doc Markdown.doc"""
    l_genus(n::Int)
Compute the total class of the L genus up to degree $n$, in terms of the
Pontryagin classes."""
l_genus(n::Int)

@doc Markdown.doc"""
    a_hat_genus(n::Int)
Compute the total class of the $\hat A$ genus up to degree $n$, in terms of the
Pontryagin classes."""
a_hat_genus(n::Int)

@doc Markdown.doc"""
    section_zero_locus(F::AbsBundle)

Construct the zero locus of a general section of a bundle $F$.

Use the argument `class=true` to only compute the class of the zero locus (same
as `ctop(F)`).
"""
function section_zero_locus(F::AbsBundle; class::Bool=false)
  X = F.parent
  R = X.ring
  cZ = ctop(F)
  # return only the class of Z in the chow ring of X
  class && return cZ
  I = Ideal(R.R, [cZ.f])
  if isdefined(R, :I)
    AˣZ = ChRing(R.R, R.w, Singular.quotient(R.I, I))
  else
    AˣZ = ChRing(R.R, R.w)
  end
  Z = AbsVariety(X.dim - F.rank, AˣZ)
  if isdefined(X, :point)
    ps = basis(Z.dim, Z) # the 0-cycles
    @assert length(ps) == 1 # make sure that the 0-cycle is unique
    p = ps[1]
    degp = integral(R(p.f) * cZ) # compute the degree of iₓp
    Z.point = Z(inv(degp) * p.f)
  end
  if isdefined(X, :T)
    Z.T = AbsBundle(Z, Z((ch(X.T) - ch(F)).f))
  end
  if isdefined(X, :O1)
    Z.O1 = Z(X.O1.f)
  end
  iₓ = x -> x.f * cZ
  iₓ = map_from_func(iₓ, Z.ring, X.ring)
  i = AbsVarietyHom(Z, X, Z.(gens(R.R)), iₓ)
  i.T = pullback(i, -F)
  Z.struct_map = i
  set_special(Z, :description => "Zero locus of a section of $F")
  return Z
end

@doc Markdown.doc"""
    complete_intersection(X::AbsVariety, degs::Int...)
    complete_intersection(X::AbsVariety, degs::Vector{Int})
Construct the complete intersection in $X$ of general hypersurfaces with
degrees $d_1,\dots,d_k$.
"""
complete_intersection(X::AbsVariety, degs::RingElement...) = complete_intersection(X, collect(degs))
complete_intersection(X::AbsVariety, degs::Vector{T}) where T <: RingElement = (
  Y = section_zero_locus(sum(OO(X, d) for d in degs));
  set_special(Y, :description => "Complete intersection of degree $(tuple(degs...)) in $X");
  Y)

@doc Markdown.doc"""
    degeneracy_locus(k::Int, F::AbsBundle, G::AbsBundle)

Construct the $k$-degeneracy locus for a general bundle map from $F$ to $G$.

Use the argument `class=true` to only compute the class of the degeneracy locus.
"""
function degeneracy_locus(k::Int, F::AbsBundle, G::AbsBundle; class::Bool=false)
  F, G = _coerce(F, G)
  m, n = rank(F), rank(G)
  @assert k < min(m,n)
  if class
    # return only the class of D in the chow ring of X
    if (m-k)*(n-k) <= F.parent.dim # Porteous' formula
      return ch(schur_functor(repeat([m-k], n-k), G-F))[(m-k)*(n-k)]
    else # expected dimension is negative
      return F.parent.ring(0)
    end
  end
  Gr = (m-k == 1) ? proj(F) : flag(m-k, F)
  S = Gr.bundles[1]
  D = section_zero_locus(dual(S) * G)
  D.struct_map = D → F.parent # skip the flag variety
  set_special(D, :description => "Degeneracy locus of rank $k from $F to $G")
  return D
end

###############################################################################
#
# Projective spaces, Grassmannians, flag varieties
#
@doc Markdown.doc"""
    point()
Construct a point as an abstract variety."""
function point(; base::Ring=QQ, param::Union{String, Vector{String}}=String[])
  base, param = _parse_base(base, param)
  R, (p,) = PolynomialRing(base, ["p"])
  I = Ideal(R, [p])
  pt = AbsVariety(0, ChRing(R, [1], I))
  pt.point = pt(1)
  pt.T = AbsBundle(pt, pt(0))
  pt.O1 = pt(0)
  set_special(pt, :description => "Point")
  set_special(pt, :point => true)
  return param == [] ? pt : (pt, param)
end

@doc Markdown.doc"""
    proj(n::Int)
Construct an abstract projective space of dimension $n$, parametrizing
1-dimensional *subspaces* of a vector space of dimension $n+1$."""
function proj(n::Int; symbol::String="h", base::Ring=QQ, param::Union{String, Vector{String}}=String[])
  base, param = _parse_base(base, param)
  R, (h,) = PolynomialRing(base, [symbol])
  I = Ideal(R, [h^(n+1)])
  AˣP = ChRing(R, [1], I)
  P = AbsVariety(n, AˣP)
  P.point = P(h^n)
  P.O1 = P(h)
  chTP = R(n)
  for i in 1:n chTP += ZZ(n+1)//factorial(ZZ(i))*h^i end
  P.T = AbsBundle(P, chTP)
  P.T.chern = P((1+h)^(n+1))
  S = AbsBundle(P, 1, 1-h)
  Q = OO(P)*(n+1) - S
  P.bundles = [S, Q]
  P.struct_map = hom(P, point(base=base), [P(1)])
  set_special(P, :description => "Projective space of dim $n")
  set_special(P, :grassmannian => :absolute)
  set_special(P, :alg => true)
  return param == [] ? P : (P, param)
end

@doc Markdown.doc"""
    proj(F::AbsBundle)
Construct the projectivization of a bundle $F$, parametrizing 1-dimensional
*subspaces*."""
function proj(F::AbsBundle; symbol::String="h")
  X, r = F.parent, F.rank
  !(r isa Int) && error("expect rank to be an integer")
  R = X.ring
  syms = vcat([symbol], string.(gens(R.R)))
  ord = ordering_dp(1) * R.R.ord
  # construct the ring
  R1, (h,) = PolynomialRing(X.base, syms, ordering=ord)
  pback = Singular.AlgebraHomomorphism(R.R, R1, gens(R1)[2:end])
  pfwd = Singular.AlgebraHomomorphism(R1, R.R, pushfirst!(gens(R.R), R.R()))
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
  S = AbsBundle(PF, 1, 1-h)
  Q = pullback(p, F) - S
  p.T = dual(S)*Q
  if isdefined(X, :T) PF.T = pullback(p, X.T) + p.T end
  PF.bundles = [S, Q]
  PF.struct_map = p
  set_special(PF, :description => "Projectivization of $F")
  set_special(PF, :grassmannian => :relative)
  return PF
end

@doc Markdown.doc"""
    grassmannian(k::Int, n::Int; bott::Bool=false)

Construct an abstract Grassmannian $\mathrm{Gr}(k, n)$, parametrizing
$k$-dimensional subspaces of an $n$-dimensional vector space.

Use the argument `bott=true` to construct the Grassmannian as a `TnVariety` for
computing integrals using Bott's formula.
"""
function grassmannian(k::Int, n::Int; bott::Bool=false, weights=:int, symbol::String="c", base::Ring=QQ, param::Union{String, Vector{String}}=String[])
  # combine the interface for AbsVariety and TnVariety versions
  bott && return tn_grassmannian(k, n, weights=weights)
  abs_grassmannian(k, n, symbol=symbol, base=base, param=param)
end

function abs_grassmannian(k::Int, n::Int; symbol::String="c", base::Ring=QQ, param::Union{String, Vector{String}}=String[])
  @assert k < n
  d = k*(n-k)
  base, param = _parse_base(base, param)
  R, c = PolynomialRing(base, _parse_symbol(symbol, 1:k))
  AˣGr = ChRing(R, collect(1:k))
  inv_c = AˣGr(sum((-sum(c))^i for i in 1:n)) # this is c(Q) since c(S)⋅c(Q) = 1
  # Q is of rank n-k: the vanishing of Chern classes in higher degrees provides all the relations for the Chow ring
  cQ = sum(inv_c[1:n-k])
  AˣGr.I = std(Ideal(R, [x.f for x in inv_c[n-k+1:n]]))
  Gr = AbsVariety(d, AˣGr)
  Gr.O1 = Gr(-c[1])
  S = AbsBundle(Gr, k, 1 + sum(c))
  Q = OO(Gr)*n - S
  Q.chern = 1 + cQ
  Gr.point = Gr((-1)^d*c[end]^(n-k))
  Gr.T = dual(S) * Q
  Gr.bundles = [S, Q]
  Gr.struct_map = hom(Gr, point(base=base), [Gr(1)])
  set_special(Gr, :description => "Grassmannian Gr($k, $n)")
  set_special(Gr, :grassmannian => :absolute)
  set_special(Gr, :alg => true)
  return param == [] ? Gr : (Gr, param)
end

@doc Markdown.doc"""
    flag(dims::Int...; bott::Bool=false)
    flag(dims::Vector{Int}; bott::Bool=false)

Construct an abstract flag variety $\mathrm{Fl}(d_1,\dots,d_k)$, parametrizing
flags of subspaces $V_{d_1}\subset V_{d_2}\subset\cdots\subset V_{d_k}=V$.

Use the argument `bott=true` to construct the flag variety as a `TnVariety` for
computing integrals using Bott's formula.
"""
function flag(dims::Int...; bott::Bool=false, weights=:int, symbol::String="c", base::Ring=QQ, param::Union{String, Vector{String}}=String[])
  # combine the interface for AbsVariety and TnVariety versions
  bott && return tn_flag(collect(dims), weights=weights)
  abs_flag(collect(dims), symbol=symbol, base=base, param=param)
end

function flag(dims::Vector{Int}; bott::Bool=false, weights=:int, symbol::String="c", base::Ring=QQ, param::Union{String, Vector{String}}=String[])
  bott && return tn_flag(dims, weights=weights)
  abs_flag(dims, symbol=symbol, base=base, param=param)
end

function abs_flag(dims::Vector{Int}; symbol::String="c", base::Ring=QQ, param::Union{String, Vector{String}}=String[])
  n, l = dims[end], length(dims)
  ranks = pushfirst!([dims[i+1]-dims[i] for i in 1:l-1], dims[1])
  @assert all(r->r>0, ranks)
  d = sum(ranks[i] * sum(dims[end]-dims[i]) for i in 1:l-1)
  base, param = _parse_base(base, param)
  syms = vcat([_parse_symbol(symbol, i, 1:r) for (i,r) in enumerate(ranks)]...)
  ord = prod(ordering_dp(r) for r in ranks)
  R = PolynomialRing(base, syms, ordering=ord)[1]
  AˣFl = ChRing(R, vcat([collect(1:r) for r in ranks]...))
  c = pushfirst!([1+sum(gens(R)[dims[i]+1:dims[i+1]]) for i in 1:l-1], 1+sum(gens(R)[1:dims[1]]))
  Rx, x = R["x"]
  gi = AˣFl(prod(c))[0:n]
  g = sum(gi[i+1].f * x^(n-i) for i in 0:n)
  q = mod(x^n, g)
  rels = [Nemo.coeff(q, i) for i in 0:n-1]
  AˣFl.I = std(Ideal(R, rels))
  Fl = AbsVariety(d, AˣFl)
  Fl.bundles = [AbsBundle(Fl, r, ci) for (r,ci) in zip(ranks, c)]
  Fl.O1 = simplify(sum((i-1)*chern(1, Fl.bundles[i]) for i in 1:l))
  Fl.point = prod(ctop(E)^dims[i] for (i,E) in enumerate(Fl.bundles[2:end]))
  Fl.T = sum(dual(Fl.bundles[i]) * sum([Fl.bundles[j] for j in i+1:l]) for i in 1:l-1)
  Fl.struct_map = hom(Fl, point(base=base), [Fl(1)])
  set_special(Fl, :description => "Flag variety Flag$(tuple(dims...))")
  if l == 2 set_special(Fl, :grassmannian => :absolute) end
  set_special(Fl, :alg => true)
  if all(r->r==1, ranks)
    set_special(Fl, :weyl_group => WeylGroup("A$(n-1)"))
    set_special(Fl, :roots => -[c[i] - c[i+1] for i in 1:n-1])
  end
  return param == [] ? Fl : (Fl, param)
end

@doc Markdown.doc"""
    flag(d::Int, F::AbsBundle)
    flag(dims::Vector{Int}, F::AbsBundle)
Construct the relative flag variety of a bundle $F$, parametrizing
flags of subspaces $V_{d_1}\subset V_{d_2}\subset\cdots\subset V_{d_k}$. The
last dimension (i.e., the rank of $F$) can be omitted.
"""
function flag(d::Int, F::AbsBundle; symbol::String="c") flag([d], F, symbol=symbol) end
function flag(dims::Vector{Int}, F::AbsBundle; symbol::String="c")
  X, n = F.parent, F.rank
  !(n isa Int) && error("expect rank to be an integer")
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
  ord = prod(ordering_dp(r) for r in ranks) * X.ring.R.ord
  R1 = PolynomialRing(X.base, syms, ordering=ord)[1]
  pback = Singular.AlgebraHomomorphism(R.R, R1, gens(R1)[n+1:end])
  pfwd = Singular.AlgebraHomomorphism(R1, R.R, vcat(repeat([R.R()], n), gens(R.R)))
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
  Fl.bundles = [AbsBundle(Fl, r, ci) for (r,ci) in zip(ranks, c)]
  section = prod(ctop(E)^sum(dims[i]) for (i, E) in enumerate(Fl.bundles[2:end]))
  if isdefined(X, :point)
    Fl.point = pback(X.point.f) * section
  end
  pˣ = Fl.(gens(R1)[n+1:end])
  pₓ = x -> X(pfwd(div(x, section).f))
  pₓ = map_from_func(pₓ, Fl.ring, X.ring)
  p = AbsVarietyHom(Fl, X, pˣ, pₓ)
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

@doc Markdown.doc"""
    schubert_class(G::AbsVariety, λ::Int...)
    schubert_class(G::AbsVariety, λ::Vector{Int})
    schubert_class(G::AbsVariety, λ::Partition)
Return the Schubert class $\sigma_\lambda$ on a (relative) Grassmannian $G$.
"""
function schubert_class(G::AbsVariety, λ::Int...) schubert_class(G, collect(λ)) end
function schubert_class(G::AbsVariety, λ::Partition) schubert_class(G, collect(λ)) end
function schubert_class(G::AbsVariety, λ::Vector{Int})
  get_special(G, :grassmannian) === nothing && error("the variety is not a Grassmannian")
  (length(λ) > rank(G.bundles[1]) || sort(λ, rev=true) != λ) && error("the Schubert input is not well-formed")
  giambelli(λ, G.bundles[2])
end

@doc Markdown.doc"""
    schubert_classes(m::Int, G::AbsVariety)
Return all the Schubert classes in codimension $m$ on a (relative) Grassmannian $G$."""
function schubert_classes(m::Int, G::AbsVariety)
  get_special(G, :grassmannian) === nothing && error("the variety is not a Grassmannian")
  S, Q = G.bundles
  [schubert_class(G, λ) for λ in partitions(m, rank(S), rank(Q))]
end
