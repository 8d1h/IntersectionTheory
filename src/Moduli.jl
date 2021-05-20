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
# 2) blowup the incidence variety i:I ↪ X to get the Hilbert scheme H
# TODO allow access to intermediate objects like i, I, and X
@doc Markdown.doc"""
    twisted_cubics()
    twisted_cubics(V::AbsBundle)

Construct the parameter space $H$ of twisted cubics in $\mathbf P^3$, or
relative to a rank-4 vector bundle $V$, as the blowup of the matrix moduli
space $X$ along $i:I\hookrightarrow X$.

Return the parameter space $H$ and the exceptional divisor $Y$.
"""
function twisted_cubics(; base::Ring=Singular.QQ) # absolute case: Hilbert scheme of twisted cubics in P³
  X = matrix_moduli(4, 2, 3, base=base)
  S, Q = proj(3, base=base).bundles
  I = proj(dual(Q))
  T, R = I.bundles
  iˣE = T * dual(Q)
  iˣF = T * dual(R) * det(dual(Q))
  image = vcat(chern(iˣE)[1:3], chern(iˣF)[1:2])
  i = hom(I, X, image, :alg)
  blowup(i)
end

function twisted_cubics(V::AbsBundle) # relative case
  @assert V.rank == 4
  B = V.parent
  X = matrix_moduli(V, 2, 3)
  PV = proj(V) # subspaces [V₁] ⊂ P(V)
  S, Q = PV.bundles
  I = proj(dual(Q)) # linear forms f that vanish on V₁
  T, R = I.bundles
  iˣE = T * dual(Q)
  iˣF = T * dual(R) * det(dual(Q))
  image = vcat(chern(iˣE)[1:3], chern(iˣF)[1:2], (I → B).pullback.(gens(B.ring)))
  i = hom(I, X, image, :alg)
  blowup(i)
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
@doc Markdown.doc"""
    matrix_moduli(q::Int, m::Int, n::Int)
    matrix_moduli(V::AbsBundle, m::Int, n::Int)

Construct the moduli space $N(q;m,n)$ of $n\times m$ matrices of linear forms
on a $q$-dimensional vector space, or relative to a rank-$q$ vector bundle $V$.
"""
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
  X.struct_map = hom(X, point(base=base))
  E, F = AbsBundle(X, n, 1 + sum(e)), AbsBundle(X, m, 1 + sum(f))
  X.T = hom(F, E * q) - (hom(E, E) + hom(F, F)) + OO(X)
  X.point = chern(X.dim, (m*q-n)*E - m*F)
  X.bundles = [F, E]
  set_special(X, :alg => true)
  set_special(X, :description => "Moduli space of $(n)x$(m) matrices of linear forms on a $(q)-dim vector space")
  X
end

function matrix_moduli(V::AbsBundle, m::Int, n::Int)
  @assert gcd(m, n) == 1
  q = V.rank
  S, AˣS = V.parent, V.parent.ring
  A = add_vars(AˣS, [n=>"e", m=>"f"], w=vcat(collect(1:n), collect(1:m)))
  e, f = gens(A)[1:n], gens(A)[n+1:n+m]
  B = add_vars(AˣS, [n=>"a", m=>"b"])
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
  p = hom(X, S, gens(A)[n+m+1:end], :alg)
  X.struct_map = p
  E, F = AbsBundle(X, n, 1 + sum(e)), AbsBundle(X, m, 1 + sum(f))
  p.T = hom(F, E * dual(V)) - (hom(E, E) + hom(F, F)) + OO(X)
  X.T = pullback(p, S.T) + p.T
  X.point = pullback(p, S.point) * chern(X.dim - S.dim, (m*q-n)*E - m*F)
  X.bundles = [F, E]
  set_special(X, :description => "Moduli space of $(n)x$(m) matrices of linear forms on $V")
  X
end

# We can compute this now! The computation should take around 5s.
@doc Markdown.doc"""
    twisted_cubics_on_quintic_threefold()

Compute the number of twisted cubics on a generic quintic threefold.
"""
function twisted_cubics_on_quintic_threefold()
  G = grassmannian(4, 5)
  V = G.bundles[1]
  X = matrix_moduli(V, 2, 3)
  F, E = X.bundles
  PV = proj(V) # subspaces [V₁] ∈ P(V)
  S, Q = PV.bundles
  I = proj(dual(Q)) # linear forms f that vanish on V₁
  T, R = I.bundles
  iˣE = T * dual(Q)
  iˣF = T * dual(R) * det(dual(Q))
  image = vcat(chern(iˣE)[1:3], chern(iˣF)[1:2], (I → G).pullback.(gens(G.ring)))
  i = hom(I, X, image, :alg)
  H, Y = blowup(i)
  A = OO(H) * symmetric_power(5, dual(V)) - (E * symmetric_power(3, dual(V)) - F * symmetric_power(2, dual(V)))
  B = pushforward(Y → H, symmetric_power(2, dual(S) + R) * det(dual(Q)) * OO(Y, -1))
  integral(chern(A - B)) # 317206375
end

# This should take around 100s.
@doc Markdown.doc"""
    twisted_cubics_on_cubic_fourfold()

Compute the Euler number of the LLSvS eightfold $Z$ associated to a cubic
fourfold.

Use the argument `M3=true` to return the 10-dimensional parameter space $M_3$
of twisted cubics on a cubic fourfold. The Euler number of $Z$ can then be
obtained as $e(Z) = \frac13e(M_3)-81$.
"""
function twisted_cubics_on_cubic_fourfold(; M3::Bool=false)
  G = grassmannian(4, 6)
  V = G.bundles[1]
  X = matrix_moduli(V, 2, 3)
  F, E = X.bundles
  PV = proj(V) # subspaces [V₁] ∈ P(V)
  S, Q = PV.bundles
  I = proj(dual(Q)) # linear forms f that vanish on V₁
  T, R = I.bundles
  iˣE = T * dual(Q)
  iˣF = T * dual(R) * det(dual(Q))
  image = vcat(chern(iˣE)[1:3], chern(iˣF)[1:2], (I → G).pullback.(gens(G.ring)))
  i = hom(I, X, image, :alg)
  H, Y = blowup(i)
  A = pushforward(Y → H, exterior_power(3, OO(I) * dual(V) - dual(S)) * OO(Y, -1))
  B = OO(H) * symmetric_power(3, dual(V)) - (E * dual(V) - F + A)
  M3 && return section_zero_locus(B)
  integral(chern(10, H.T - B) * ctop(B)) // 3 - 81
end
