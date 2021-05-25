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
    variety $\mathrm{Fl}(1,2,\dots,n)$ is available.

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
