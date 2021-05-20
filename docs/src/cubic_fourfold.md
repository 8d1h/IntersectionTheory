```@meta
CurrentModule = IntersectionTheory
DocTestSetup = quote
  using IntersectionTheory
end
```
```@setup repl
using IntersectionTheory
```
# Special cubic fourfolds
Cubic fourfolds are degree-3 smooth hypersurfaces in $\mathbf P^5$. They can be
constructed using `complete_intersection`.
```@repl repl
Y = complete_intersection(proj(5), 3)
basis(Y)
```
We see that a generic $Y$ only contains classes that are complete
intersections.

Special cubic fourfolds are those that contain a surface not homologous to a complete
intersection, i.e. they have extra algebraic classes.
We can construct a surface $S$ as follows.
```@repl repl
S, (h, c1, c2) = variety(2, ["h", "c1", "c2"], [1, 1, 2])
S.T = bundle(S, 2, 1 + c1 + c2)
trim!(S.ring);
basis(S)
```
Here we first built a generic 2-dimensional variety with some classes, then we
specified its tangent bundle. The step `trim!` is to get rid of classes that
have codimension larger than 2.

Now we build the inclusion.
```@repl repl
i = hom(S, Y, [h])
```
The self-intersection number of $S$ in $Y$ is equal to the top Chern class of
the normal bundle, while this latter can be accessed as the negative of the
relative tangent bundle of $i$.
```@repl repl
ctop(-i.T)
```
Since we saw that there is no algebraic class in $Y$ for the surface $S$, the
classes on $S$ cannot be pushforward to $Y$.
```@repl repl
pushforward(i, S(1))
```
To overcome this we may use the argument `inclusion=true` when building the
inclusion. The returned inclusion will then have its codomain a modified
version of $Y$, with extra classes added.
```@repl repl
j = hom(S, Y, [h], inclusion=true, symbol="s")
Y₁ = j.codomain
basis(Y₁)
```
Now we can pushforward classes on $S$.
```@repl repl
pushforward(j, S(1))
pushforward(j, ctop(-j.T))
```

## Cubic fourfolds containing a degree-5 del Pezzo surface
We compute with a more explicit surface. A degree-5 del Pezzo surface can be
constructed as the projective plane blown up at 4 points.
```@repl repl
S = blowup_points(4, proj(2))
basis(S)
```
It can be embedded in a special cubic fourfold $Y_1$ via the anti-canonical
linear system.
```@repl repl
K = canonical_class(S)
chi(OO(S, -K))
i = hom(S, Y, [-K], inclusion=true, symbol="s")
Y₁ = i.codomain
```
The cubic fourfold is rational in this case: a rational map to $\mathbf P^4$
can be given by the linear system of quadric hypersurfaces containing $S$.
Numerically, we compute the blowup of $Y_1$ along $S$ and study the divisor
$2h-e$.
```@repl repl
Bl, E = blowup(i)
h = pullback(Bl → Y₁, Y₁.O1)
e = pushforward(E → Bl, E(1))
integral((2h - e)^4)
chi(OO(Bl, 2h - e))
```
