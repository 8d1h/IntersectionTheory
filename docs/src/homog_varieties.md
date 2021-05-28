```@meta
CurrentModule = IntersectionTheory
DocTestSetup = quote
  using IntersectionTheory
end
```
```@setup repl
using IntersectionTheory
```
# Homogeneous varieties
!!! note
    This part is still under developement. Right now only the complete flag
    varieties of type A, B, C, D are available.

## Weyl groups
Elements are represented as permutation cycles.

### Examples
```@repl repl
W = weyl_group("A3")
W()
W([1,2])
W(perm([2,1,3,4]))
length(ans)
basis(W)
betti(W)
ans == betti(flag(1,2,3,4))
longest_element(W)
gens(W)
W[2]
```
Parabolic subgroups.
```@repl repl
weyl_group("A4", [1,2,4])
betti(weyl_group("A4")) ÷ betti(weyl_group("A4", [1,2,4]))
ans == betti(grassmannian(3, 5))
```
## Homogeneous varieties
Only complete flag varieties $G/B$ of type A, B, C, D are available for now.
```@repl repl
homogeneous_variety("B3")
homogeneous_variety("C3")
F = homogeneous_variety("D3")
euler(F)
betti(F)
```
Integral on partial flag varieties (temporary work-around; should be able to
construct these directly).
```@repl repl
G = homogeneous_variety("C3")
U = sum(G.bundles[1:2])           # U on IGr(2, 6)
O1 = det(dual(U))
Q = 6OO(G) - U
F = (dual(Q) - U) * O1 + O1^3     # case (sb0)
integral(todd(G.T - F) * ctop(F)) # chi(O_Y)
```
## Schubert classes
Let $F:=\mathrm{Fl}(1,2,\dots,n)$ be a complete flag variety. Its Weyl group
$W$ is isomorphic to the symmetric group $\mathfrak S_n$.
For an element $w\in W$ of length $l(w)$, the Schubert variety $X_w$ is a
subvariety of dimension $l(w)$. The following returns its class
$\sigma_w:=[X_w]$ as an element of the Chow ring. The underlying polynomial is
also known as a *Schubert polynomial*.
```@docs
schubert_class(F::AbsVariety, w::WeylGroupElem)
```
### Examples
```@repl repl
F = flag(1,2,3,4,5)
W = weyl_group(F)
w0 = longest_element(W)
schubert_class(F, w0)
w = W([1,2], [3,4,5])
schubert_class(F, w)
```
The classes $\sigma_w$ and $\sigma_{ww_0}$ are Poincaré dual to each other.
```@repl repl
integral(schubert_class(F, w) * schubert_class(F, w * w0))
```
For $w$ of length 1, $\sigma_w$ is the class of a rational curve.
```@repl repl
integral(schubert_class(F, W[1]) * F.O1)
```
Similar results hold for other types of complete flag varieties.
```@repl repl
F = homogeneous_variety("B3")
W = weyl_group(F)
w0 = longest_element(W)
schubert_class(F, w0)
schubert_class(F, W())
ans == F.point
```
