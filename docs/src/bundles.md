```@meta
CurrentModule = IntersectionTheory
DocTestSetup = quote
  using IntersectionTheory
end
```
```@setup repl
using IntersectionTheory
```
# Bundles
We try to keep the same syntax for `AbsBundle` and `TnBundle`. Note that not
all methods are available for `TnBundle`.
## Construct bundles
```@docs
bundle
OO
bundles
tangent_bundle(X::AbsVariety)
cotangent_bundle(X::AbsVariety)
canonical_bundle
canonical_class
```
### Examples
```@repl repl
OO(proj(2))
bundles(grassmannian(2, 4))
bundles(grassmannian(2, 4, bott=true))
tangent_bundle(variety(3))
```
## Characteristic classes
```@docs
ch
chern(F::AbsBundle)
chern(k::Int, F::AbsBundle)
ctop
segre
chi
todd(F::AbsBundle)
pontryagin(F::AbsBundle)
pontryagin(k::Int, F::AbsBundle)
```
!!! note
    For a `TnBundle` of rank $r$, since there are no Chow ring present, its
    Chern classes are represented as formal polynomials in $r$ variables.
    Arithmetics are only available for Chern classes of a same `TnBundle`.
    See examples below.
### Examples
For `AbsBundle`.
```@repl repl
X, (F,) = variety(2, [2=>"c"]);
ch(F)
chern(F)
pontryagin(F)
chern(proj(2))
chern(2, proj(2))
todd(proj(2))
chi(cotangent_bundle(proj(2)))
G = grassmannian(2, 4); S, Q = bundles(G);
chern(1, S)
integral(chern(1, S)^4)
chern(1, S) * chern(2, Q)
```
For `TnBundle`.
```@repl repl
G = grassmannian(2, 4, bott=true); S, Q = bundles(G);
chern(1, S)
integral(chern(1, S)^4)
chern(1, S) * chern(2, Q) # this will not work
```
## Operators
```@docs
symmetric_power
exterior_power
det
dual
schur_functor
```
