###############################################################################
#
# given a finite ChAlgHom f:A → B, realize B as an A-module by computing a
# representation matrix M such that Aⁿ —M→ Aᵍ —ϕ→ B → 0
# returns a tuple (M, gensB, pf) where
#   M is the representation matrix;
#   gensB are generators of B as A-module, i.e. the matrix of ϕ;
#   pf maps an element of B back to a vector in Aᵍ, i.e. a section of ϕ.
# gensB is obtained using `kbase`, so the last one is always 1
#
function _pushfwd(f::ChAlgHom)
  A, B, M = f.domain, f.codomain, [x.f for x in f.image]
  @assert base_ring(A.R) == base_ring(B.R)
  base = base_ring(A.R)
  symsA, symsB = string.(gens(A.R)), string.(gens(B.R))
  a, b = length(symsA), length(symsB)
  # the ring for the graph of f
  # ord = ordering_dp(b) * ordering_dp(a)
  ord = ordering_wp(B.w) * ordering_wp(A.w)
  R, ba = PolynomialRing(base, vcat(symsB, symsA), ordering=ord)
  AtoR = Singular.AlgebraHomomorphism(A.R, R, ba[b+1:end])
  BtoR = Singular.AlgebraHomomorphism(B.R, R, ba[1:b])
  RtoA = Singular.AlgebraHomomorphism(R, A.R, vcat(repeat([A.R()], b), gens(A.R)))
  I = std(Ideal(B.R, isdefined(B, :I) ? vcat(gens(B.I), M) : M))
  Singular.dimension(I) > 0 && error("not a finite algebra extension")
  gensB = gens(Singular.kbase(I)) # generators of B as A-module
  @assert gensB[end] == 1 # the last one should always be 1
  g = length(gensB)
  gensB_lift = [R(BtoR(g)) for g in gensB]
  # compute the ideal J of the graph of f
  rels = [R(ba[b+i]-BtoR(m)) for (i,m) in enumerate(M)]
  if isdefined(A, :I) for g in gens(A.I) push!(rels, R(AtoR(g))) end end
  if isdefined(B, :I) for g in gens(B.I) push!(rels, R(BtoR(g))) end end
  J = std(Ideal(R, rels)) # the ideal of the graph of f
  pf = x -> (y = Singular.reduce(R(BtoR(x)), J);
	     ans = Nemo.elem_type(A.R)[];
	     for i in 1:g
	       q = div(y, gensB_lift[i])
	       push!(ans, RtoA(q))
	       y -= q * gensB_lift[i]
	     end; ans)
  F = Singular.FreeModule(R, g)
  gB = [F(push!([j == i ? R(1) : R() for j in 1:g-1], -gensB_lift[i])) for i in 1:g-1]
  gJ = [F([j==i ? x : R() for j in 1:g]) for x in gens(J) for i in 1:g]
  # XXX this is slow
  P = std(Singular.Module(R, gB..., gJ...)) # the presentation matrix, as an R-module
  # use a new weight to do elimination
  Rw = ChRing(R, vcat(repeat([1], b), repeat([0], a)))
  inA = x -> total_degree(Rw(x)) <= 0
  M = hcat([(RtoA.(Array(P[i]))) for i in 1:Singular.ngens(P) if all(inA, Array(P[i]))]...)
  return M, gensB, pf
end

###############################################################################
#
# Blowup
#
# notations are as follows: given an inclusion i:X → Y, we blowup X in Y
# 
#   PN ———j——→ Bl
#    |          |
#    g          f
#    ↓          ↓
#    X ———i———→ Y
# 
# 0 → AˣX → AˣPN ⊕ AˣY → AˣBl → 0 is a short exact sequence
# AˣPN is generated as an AˣX-module by powers of the relative O(1)-class ζ
# AˣX is generated as an AˣY-module by x[1],…,x[n], computed using `_pushfwd`
# AˣBl is generated as an AˣY-algebra by the images of these generators under jₓgˣ
# they will be denoted by E[i] := jₓgˣ(x[i])
# in particular, the last E = E[end] is the class jₓgˣ1 of the exceptional divisor E
# and we have jˣE[end] = -ζ
# the projection formula gives jₓ(gˣx ⋅ ζᵏ) = jₓ(gˣx) ⋅ (-E[end])ᵏ
#
@doc Markdown.doc"""
    blowup(i::AbsVarietyHom)

Construct the blowup $\mathrm{Bl}_XY$ of an inclusion $i:X\hookrightarrow Y$.

Return the variety $\mathrm{Bl}$ and the exceptional divisor $E$.
"""
function blowup(i::AbsVarietyHom; symbol::String="e")
  X, Y = i.domain, i.codomain
  N = -i.T # normal bundle
  d = rank(N) # codimension of X in Y
  d <= 0 && error("not a proper subvariety")
  AˣY, RY = Y.ring, Y.ring.R
  M, x, pf = _pushfwd(i.pullback)
  n = length(x)
  # the last variable E is the class of the exceptional divisor
  syms = vcat(push!(_parse_symbol(symbol, 1:n-1), symbol), string.(gens(RY)))
  degs = [total_degree(X(x[i])) + 1 for i in 1:n]
  RBl = PolynomialRing(Y.base, syms)[1]
  E, y = gens(RBl)[1:n], gens(RBl)[n+1:end]
  fˣ = Singular.AlgebraHomomorphism(RY, RBl, y)
  jₓgˣ = x -> sum(E .* fˣ.(pf(x.f)))
  rels = Singular.spoly[]
  # now we determine the relations in AˣBl
  # 1) relations from Y
  if isdefined(AˣY, :I)
    for r in fˣ.(gens(AˣY.I)) push!(rels, r) end
  end

  # 2) relations for AˣX as an AˣY-module
  for r in E' * fˣ.(M) push!(rels, r) end

  # 3) jₓx ⋅ jₓy = -jₓ(x⋅y⋅ζ)
  # recall that E[i] = jₓgˣ(x[i])
  for j in 1:n-1, k in j:n-1
    push!(rels, E[j] * E[k] + jₓgˣ(X(x[j] * x[k])) * (-E[end]))
  end
  
  # 4) relation for AˣPN: ∑ gˣcₖ(N) ⋅ ζᵈ⁻ᵏ = 0
  cN = chern(N)[0:d] # cN[k] = cₖ₋₁(N)
  push!(rels, sum([jₓgˣ(cN[k+1]) * (-E[end])^(d-k) for k in 0:d]))

  # 5) fˣiₓx = jₓ(gˣx ⋅ ctop(Q)) where Q is the tautological quotient bundle on PN
  # we have ctop(Q) = ∑ gˣcₖ₋₁(N) ⋅ ζᵈ⁻ᵏ
  for j in 1:n
    lhs = fˣ(i.pushforward(X(x[j])).f) # this is the crucial step where iₓ is needed
    rhs = sum([jₓgˣ(x[j] * cN[k]) * (-E[end])^(d-k) for k in 1:d])
    push!(rels, lhs - rhs)
  end

  AˣBl = ChRing(RBl, vcat(degs, AˣY.w), Ideal(RBl, rels...))
  Bl = AbsVariety(Y.dim, AˣBl)
  # Bl being constructed, we add the morphisms f, g, and j
  RBltoRY = Singular.AlgebraHomomorphism(RBl, RY, vcat(repeat([RY()], n), gens(RY)))
  fₓ = x -> (xf = simplify(x).f;
	     Y(RBltoRY(xf));)
  fₓ = map_from_func(fₓ, Bl.ring, Y.ring)
  f = AbsVarietyHom(Bl, Y, Bl.(y), fₓ)
  Bl.struct_map = f
  if isdefined(Y, :point) Bl.point = f.pullback(Y.point) end
  PN = proj(N) # the exceptional divisor as the projectivization of N
  g = PN.struct_map
  ζ = g.O1
  jˣ = vcat([-ζ * g.pullback(X(xi)) for xi in x], [g.pullback(i.pullback(f)) for f in gens(AˣY)])
  # pushforward of j: write as a polynomial in ζ, and compute term by term
  RX = X.ring.R
  RPNtoRX = Singular.AlgebraHomomorphism(PN.ring.R, RX, pushfirst!(gens(RX), RX()))
  jₓ = x -> (xf = simplify(x).f;
	     RX = X.ring.R; ans = RBl();
	     for k in d-1:-1:0
	       q = div(xf, ζ.f^k)
	       ans += jₓgˣ(X(RPNtoRX(q))) * (-E[end])^k
	       xf -= q * ζ.f^k
	     end; Bl(ans))
  jₓ = map_from_func(jₓ, PN.ring, Bl.ring)
  j = AbsVarietyHom(PN, Bl, jˣ, jₓ)
  # the normal bundle of E in Bl is O(-1)
  j.T = -PN.bundles[1]
  # finally, compute the tangent bundle of Bl
  # 0 → Bl.T → fˣ(Y.T) → jₓ(Q) → 0 where Q is the tautological quotient bundle
  f.T = -pushforward(j, PN.bundles[2])
  Bl.T = pullback(f, Y.T) + f.T
  # chern(Bl.T) can be readily computed from its Chern character, but the following is faster
  α = sum(sum((binomial(ZZ(d-j), ZZ(k)) - binomial(ZZ(d-j), ZZ(k+1))) * ζ^k for k in 0:d-j) * g.pullback(chern(j, N)) for j in 0:d)
  Bl.T.chern = simplify(f.pullback(chern(Y.T)) + j.pushforward(g.pullback(chern(X.T)) * α))
  set_special(PN, :projections => [j, g])
  set_special(Bl, :exceptional_divisor => PN)
  set_special(Bl, :description => "Blowup of $Y with center $X")
  if get_special(X, :alg) == true && get_special(Y, :alg) == true
    set_special(Bl, :alg => true)
  end
  return Bl, PN
end

@doc Markdown.doc"""
    blowup_points(n::Int, X::AbsVariety)
Construct the blowup of $X$ at $n$ points.
"""
function blowup_points(n::Int, X::AbsVariety; symbol::String="e")
  Bl = X
  symbs = _parse_symbol(symbol, 1:n)
  for i in 1:n
    Bl = blowup(point() → Bl, symbol=symbs[i])[1]
  end
  set_special(Bl, :description => "Blowup of $X at $n points")
  Bl.struct_map = hom(Bl, X)
  if get_special(X, :alg) == true
    set_special(Bl, :alg => true)
  end
  return Bl
end

###############################################################################
#
# given an AbsVarietyHom i:X → Y, declare that it is an inclusion and return a
# new one where pushforward is possible, by adding the extra classes to Y
# this results in a modified Y⁺ which represents the same variety Y but
# contains more classes
# 
#     j  Y⁺ f
#      ↗   ↘
#    X ——i—→ Y
# 
# specifically,
# AˣX is generated as an AˣY-module by x[1],…,x[n], computed using `_pushfwd`
# AˣY⁺ is generated as an AˣY-algebra by the images of these generators under jₓ
# E[i] := jₓ(x[i])
#
function _inclusion(i::AbsVarietyHom; symbol::String="x")
  X, Y = i.domain, i.codomain
  N = -i.T # normal bundle
  d = rank(N) # codimension of X in Y
  d <= 0 && error("not a proper subvariety")
  c = ctop(N)
  AˣY, RY = Y.ring, Y.ring.R
  M, x, pf = _pushfwd(i.pullback)
  n = length(x)
  # similar to blowup: the last variable is the class of X in Y
  syms = vcat(push!(_parse_symbol(symbol, 1:n-1), symbol), string.(gens(RY)))
  degs = [total_degree(X(x[i])) + d for i in 1:n]
  RY⁺ = PolynomialRing(Y.base, syms)[1]
  E, y = gens(RY⁺)[1:n], gens(RY⁺)[n+1:end]
  fˣ = Singular.AlgebraHomomorphism(RY, RY⁺, y)
  jₓ = x -> sum(E .* fˣ.(pf(x.f)))
  rels = Singular.spoly[]
  # we determine the relations in AˣY⁺
  # 1) relations from Y
  if isdefined(AˣY, :I)
    for r in fˣ.(gens(AˣY.I)) push!(rels, r) end
  end

  # 2) relations for AˣX as an AˣY-module
  for r in E' * fˣ.(M) push!(rels, r) end

  # 3) jₓx ⋅ jₓy = jₓ(x⋅y⋅c)
  for j in 1:n, k in j:n
    push!(rels, E[j] * E[k] - jₓ(x[j] * x[k] * c))
  end
  
  # 4) the points are the same
  if isdefined(X, :point) && isdefined(Y, :point)
    push!(rels, fˣ(Y.point.f) - jₓ(X.point))
  end
  
  AˣY⁺ = ChRing(RY⁺, vcat(degs, AˣY.w), Ideal(RY⁺, rels...))
  Y⁺ = AbsVariety(Y.dim, AˣY⁺)
  # trim!(Y⁺.ring) TODO is this necessary?
  set_special(Y⁺, :description => "$Y")
  fₓ = map_from_func(x -> error("not defined"), Y⁺.ring, Y.ring)
  f = AbsVarietyHom(Y⁺, Y, Y⁺.(y), fₓ)
  Y⁺.struct_map = f
  Y⁺.T = pullback(f, Y.T)
  f.T = AbsBundle(Y⁺, Y⁺(0)) # there is no relative tangent bundle
  Y⁺.point = f.pullback(Y.point)
  if isdefined(Y, :O1) Y⁺.O1 = f.pullback(Y.O1) end
  jˣ = vcat(X.(x) .* c, [i.pullback(f) for f in gens(AˣY)])
  j_ = map_from_func(x -> Y⁺(jₓ(x)), X.ring, Y⁺.ring)
  j = AbsVarietyHom(X, Y⁺, jˣ, j_)
  return j
end
