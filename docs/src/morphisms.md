```@meta
CurrentModule = IntersectionTheory
DocTestSetup = quote
  using IntersectionTheory
end
```
```@setup repl
using IntersectionTheory
```
# Morphisms
## Construct morphisms
A variety morphism can be built using the function `hom`.
```@docs
hom(X::AbsVariety, Y::AbsVariety, fˣ::Vector, fₓ=nothing)
```
The pullback is relatively easy to describe since it's functorial, while the
pushforward is usually more complicated. In some cases, the pushforward can be
automatically computed from the pullback. Specifically, the projection formula
tells us
```math
\forall x\in A^*(X),y\in A^*(Y)\quad f_*(x\cdot f^*y) = f_*x\cdot y.
```
Since we are working with numerical equivalence, to determine $f_*x$, it
suffices to know all its intersection numbers, which can readily be computed
using the pullback. However, for this to work, it is important that all the
algebraic classes of $Y$ are present (or at least those having non-zero
intersection numbers with $f_*x$). This is the case in the following situations:
- When $Y$ is a point or a curve;
- When all the algebraic classes on $Y$ are known, which can be declared by using `set_special(Y, :alg => true)`;
- When `:alg` is passed as the fourth argument. This can be used when we are certain
  that the pushforward computed is correct, even though not all classes on $Y$
  are present.
In other cases, a warning will be given if one tries to do pushforward.
### Examples
#### Veronese embeddings and Segre embeddings
```@repl repl
P2 = proj(2)
chi(OO(P2, 2))
v = hom(P2, proj(5), [2P2.O1])
```
```@repl repl
P = proj(2)
PxP = P * P
chi(OO(PxP, 1))
s = hom(PxP, proj(8), [PxP.O1])
```
#### Inclusion of the diagonal in the product
We create two copies of $\mathbf P^2$ so that they have different variables.
```@repl repl
Ph, Pk = proj(2, symbol="h"), proj(2, symbol="k")
PxP = Ph * Pk
D = proj(2) # the diagonal
i = hom(D, PxP, [D.O1, D.O1])
pushforward(i, D(1)) # the class of the diagonal
```
#### A "non-algebraic" example
Here is an example to illustrate what can go wrong when we try to pushforward
"non-algebraic" classes, i.e., classes that are not present.

Consider a cubic surface $S$. We can build it in two ways:
- We can build it as a (hyper)surface in $\mathbf P^3$, then in codimension 1
  we only get the class of a (hyper)plane section.
```@repl repl
S1 = complete_intersection(proj(3), 3)
basis(S1)
```
- We can realize it as $\mathbf P^2$ blown up at 6 points, so the cohomology is
  entirely algebraic with Betti numbers 1,7,1.
```@repl repl
S2 = blowup_points(6, proj(2))
basis(S2)
```
The linear system on $S_2$ that provides the embedding into $\mathbf P^3$ can
be given by $H:=3h-\sum e_i$.
```@repl repl
e, h = gens(S2)[1:6], gens(S2)[end]
H = 3h - sum(e)
chi(OO(S2, H))
integral(H^2)
```
This means that we can define a map $f:S_2\to S_1$ which is in fact an
isomorphism.
```@repl repl
f = hom(S2, S1, [H])
f.dim, ch(f.T) # the relative tangent bundle is trivial
```
But we won't be able to pushforward classes on $S_2$ to $S_1$, since they are
not present in $S_1$ hence "non-algebraic".
```@repl repl
pushforward(f, e[1])
```
We received a warning and the result is indeed wrong: the exceptional divisors
are not homologous to complete intersections.

## Canonically defined morphisms
```@docs
hom(X::AbsVariety, Y::AbsVariety)
```
Using `hom(X, Y)` (or `X → Y`) without other arguments will try to find a
canonically defined morphism from $X$ to $Y$. This means
- Either $X$ or $Y$ is a point;
- When $X$ is a product of $Y$ with some other variety, so we have a projection
  map;
- When $X$ is a projective / relative flag bundle over $Y$ (in other words, one
  can arrive at $Y$ by following the chain of structure maps from $X$).
In *Schubert2*, this is the operator `X / Y`. We will however use the symbol `X
→ Y` instead, which can be typed using the LaTeX-like abbreviation `X \to[tab] Y`.

### Examples
#### Products
```@repl repl
P, Q = proj(1), proj(1)
PxQ = P * Q
PxQ → P
```
Note that if we use `PxP = P * P`, then we will only be able to get the first
projection using `PxP → P` since we cannot distinguish the two components.
Alternatively we can retrieve the two projections using `get_special(PxQ,
:projections)` or `PxQ.other[:projections]`.
```@repl repl
PxQ.other[:projections]
```

#### Structure map
```@repl repl
X, (E,) = variety(2, [3 => "c"])
PE = proj(E)
PE → X
```
The structure maps are also used for coercion of bundles. For example, in the
above case we can pullback bundles by tensoring with the structure sheaf of
$\mathbf P(E)$.
```@repl repl
OO(PE) * E
```

## Operators
```@docs
pullback
pushforward
*(f::AbsVarietyHom, g::AbsVarietyHom)
dim(f::AbsVarietyHom)
tangent_bundle(f::AbsVarietyHom)
cotangent_bundle(f::AbsVarietyHom)
todd(f::AbsVarietyHom)
```
## Blowup
```@docs
blowup
```
Note that the exceptional divisor is returned as an abstract variety. To get
its class in the blowup, we can use `pushforward(E → Bl, E(1))`.
### Examples
```@repl repl
P = proj(2)
Bl, E = blowup(point() → P)
euler(Bl)
e = pushforward(E → Bl, E(1))
integral(e^2)
```
Here is the solution to Steiner's problem.
```@repl repl
P2, P5 = proj(2), proj(5)
v = hom(P2, P5, [2P2.O1]) # the Veronese embedding
Bl, E = blowup(v)
h = pullback(Bl → P5, P5.O1)
e = pushforward(E → Bl, E(1))
integral((6h - 2e)^5)
```
