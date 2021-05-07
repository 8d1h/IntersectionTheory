# 1) given a rank-4 bundle V over the base B, compute the relative variety p:X → B
# parameterizing nets of quadrics on P(V) (3-dim family of degree-2 forms) that
# are determinantal (coming from the 2-minors of a 3x2 matrix of linear forms)
#
# X can be realized as the GIT quotient of the space of 3x2 matrices by GL(3)xGL(2)
# 
#    Y ——q—→ X
#            |
#            p
#            ↓
#        V → B
#
# 2) blowup the incidence variety f:I ↪ X to get the Hilbert scheme H
# TODO allow access to intermediate objects like f, I, and X
function cubics(; base::Ring=Singular.QQ) # absolute case: Hilbert scheme of twisted cubics in P³
  X = matrix_moduli(4, 2, 3; base=base)
  S, Q = proj(3; base=base).bundles
  I = proj(dual(Q))
  fˣE = I.bundles[1] * dual(Q)
  fˣF = I.bundles[1] * dual(I.bundles[2]) * det(dual(Q))
  image = vcat(chern(fˣE)[1:3], chern(fˣF)[1:2])
  f = hom(I, X, image, :alg)
  blowup(f)[1]
end

function cubics(V::AbsBundle) # relative case
  @assert V.rank == 4
  B = V.parent
  X = matrix_moduli(V, 2, 3)
  PV = proj(V) # subspaces [V₁] ⊂ P(V)
  S, Q = PV.bundles
  I = proj(dual(Q)) # linear forms f that vanish on V₁
  fˣE = I.bundles[1] * dual(Q)
  fˣF = I.bundles[1] * dual(I.bundles[2]) * det(dual(Q))
  image = vcat(chern(fˣE)[1:3], chern(fˣF)[1:2], (I → B).pullback.(gens(B.ring)))
  f = hom(I, X, image, :alg)
  blowup(f)
end

# construct the space of nxm matrices with entries being 1-forms on a q-dim
# vector space V, quotient by the action of GL(m)xGL(n)
# 
#     Fₘ → Eₙ ⊗ Vᵛ
# 
# when m = 1 this gives the Grassmannian Gr(n, q)
# TODO maybe needs a better name
# TODO it appears that the result works more generally for any moduli space of
# representations of an acyclic quiver
function matrix_moduli(q::Int, m::Int, n::Int; base::Ring=Singular.QQ)
  @assert gcd(m, n) == 1 # otherwise there will be strictly semistable points
  Rᵂ, ef = PolynomialRing(base, vcat(_parse_symbol("e", 1:n), _parse_symbol("f", 1:m)))
  e, f = ef[1:n], ef[n+1:end]
  A = ChRing(Rᵂ, vcat(collect(1:n), collect(1:m)))
  R, ab = PolynomialRing(base, vcat(_parse_symbol("a", 1:n), _parse_symbol("b", 1:m)))
  a, b = ab[1:n], ab[n+1:end]
  B = ChRing(R, repeat([1], n+m))
  syma = [sum(prod(a[j] for j in c) for c in combinations(n, i)) for i in 1:n]
  symb = [sum(prod(b[j] for j in c) for c in combinations(m, i)) for i in 1:m]
  p = ChAlgHom(A, B, vcat(syma, symb))
  Y = AbsVariety(m*n*q-n^2-m^2+1, B)
  rels = [e[1] - f[1]]
  pf = _pushfwd(p)[3]
  # relations imposed by the stability condition:
  # any Fⱼ → Eₖ ⊗ Vᵛ with rank(Fⱼ) = j and rank(Eₖ) = k should have j/k > m/n
  # so for a bigger k, Fⱼ → (E/Eₖ) ⊗ Vᵛ must be nowhere vanishing
  # therefore it will have trivial top Chern class
  for j in 1:m
    k = Int(ceil(n*j//m)) - 1
    F_sub = AbsBundle(Y, j, prod(1+b[i] for i in 1:j))
    E_quo = AbsBundle(Y, n-k, prod(1+a[i] for i in k+1:n))
    for x in pf(ctop(hom(F_sub, E_quo * q)).f) push!(rels, x) end
  end
  add_rels!(A, rels)
  X = AbsVariety(Y.dim, A)
  trim!(X.ring)
  X.struct_map = hom(X, point(base=base))
  E, F = AbsBundle(X, n, 1 + sum(e)), AbsBundle(X, m, 1 + sum(f))
  X.T = hom(F, E * q) - (hom(E, E) + hom(F, F)) + OO(X)
  X.point = chern(X.dim, (m*q-n)*E - m*F)
  X.bundles = [E, F]
  set_special(X, :alg => true)
  X
end

function matrix_moduli(V::AbsBundle, m::Int, n::Int)
  @assert gcd(m, n) == 1
  q = V.rank
  S, AˣS = V.parent, V.parent.ring
  A = add_vars(add_vars(AˣS, m, symbol="f", w=collect(1:m)), n, symbol="e", w=collect(1:n))
  e, f = gens(A)[1:n], gens(A)[n+1:n+m]
  B = add_vars(add_vars(AˣS, m, symbol="b"), n, symbol="a")
  a, b, rest = gens(B)[1:n], gens(B)[n+1:n+m], gens(B)[n+m+1:end]
  syma = [sum(prod(a[j] for j in c) for c in combinations(n, i)) for i in 1:n]
  symb = [sum(prod(b[j] for j in c) for c in combinations(m, i)) for i in 1:m]
  p = ChAlgHom(A, B, vcat(syma, symb, rest))
  Y = AbsVariety(S.dim+m*n*q-n^2-m^2+1, B)
  Y.struct_map = hom(Y, S, rest)
  rels = [(e[1] - f[1]).f]
  pf = _pushfwd(p)[3]
  for j in 1:m
    k = Int(ceil(n*j//m)) - 1
    F_sub = AbsBundle(Y, j, prod(1+b[i] for i in 1:j))
    E_quo = AbsBundle(Y, n-k, prod(1+a[i] for i in k+1:n))
    for x in pf(ctop(hom(F_sub, E_quo * dual(V))).f) push!(rels, x) end
  end
  add_rels!(A, rels)
  X = AbsVariety(Y.dim, A)
  trim!(X.ring)
  p = hom(X, S, gens(A)[n+m+1:end], :alg)
  X.struct_map = p
  E, F = AbsBundle(X, n, 1 + sum(e)), AbsBundle(X, m, 1 + sum(f))
  p.T = hom(F, E * dual(V)) - (hom(E, E) + hom(F, F)) + OO(X)
  X.T = pullback(p, S.T) + p.T
  X.point = pullback(p, S.point) * chern(X.dim - S.dim, (m*q-n)*E - m*F)
  X.bundles = [E, F]
  X
end

# We can compute this now! But GC needs to be turned off, otherwise there will
# be segfaults. Also it is really slow.
function cubics_on_quintic()
  P = proj(4)
  V = dual(P.bundles[2])
  X = matrix_moduli(V, 2, 3)
  PV = proj(V) # subspaces [V₁] ⊂ P(V)
  S, Q = PV.bundles
  I = proj(dual(Q)) # linear forms f that vanish on V₁
  fˣE = I.bundles[1] * dual(Q)
  fˣF = I.bundles[1] * dual(I.bundles[2]) * det(dual(Q))
  image = vcat(chern(fˣE)[1:3], chern(fˣF)[1:2], (I → P).pullback.(gens(P.ring)))
  f = hom(I, X, image, :alg)
  H, Ex = blowup(f)
  E, F = X.bundles
  A = F * symmetric_power(2, dual(V)) - E * symmetric_power(3, dual(V)) + symmetric_power(5, dual(V))
  B = pushforward(Ex → H, symmetric_power(2, dual(S) + I.bundles[2]) * det(dual(Q)) * OO(Ex, -Ex.O1))
  integral(chern(A-B)) # 317206375
end
