```@meta
CurrentModule = IntersectionTheory
DocTestSetup = quote
  using IntersectionTheory
end
```
```@setup repl
using IntersectionTheory
```
# Varieties
## Basic invariants
```@docs
degree
euler
hilbert_polynomial
signature
```
### Examples
```@repl repl
degree(grassmannian(2, 4))
euler(grassmannian(2, 4))
hilbert_polynomial(proj(3))
signature(complete_intersection(proj(3), 4)) # signature of a K3 surface
```
## Characteristic classes
By common abuse of notations, the Chern/Todd/... class of a variety will mean
the Chern/Todd/... class of its tangent bundle.
```@docs
chern(X::AbsVariety)
chern(k::Int, X::AbsVariety)
chern_number
chern_numbers
todd(X::AbsVariety)
pontryagin(X::AbsVariety)
pontryagin(k::Int, X::AbsVariety)
a_hat_genus(X::AbsVariety)
a_hat_genus(k::Int, X::AbsVariety)
l_genus(X::AbsVariety)
l_genus(k::Int, X::AbsVariety)
```
We also have the following functions for producing generic formulae.
```@docs
todd(n::Int)
a_hat_genus(n::Int)
l_genus(n::Int)
```
### Examples
```@repl repl
chern(proj(2))
todd(proj(2))
pontryagin(proj(2))
chern_number(proj(3), [2,1])
chern_numbers(proj(3))
l_genus(proj(2))
a_hat_genus(proj(2))
```
```@repl repl
todd(2)
a_hat_genus(2)
l_genus(2)
```
## Chow ring
```@docs
basis
betti
integral
dual_basis
intersection_matrix
```
Methods for Grassmannians.
```@docs
schubert_class
schubert_classes
```
### Examples
```@repl repl
basis(proj(2))
G = grassmannian(2, 4)
basis(G)
dual_basis(G)
betti(G)
basis(2, G)
intersection_matrix(basis(2, G))
intersection_matrix(basis(2, G), dual_basis(2, G))
intersection_matrix(G)
schubert_class(G, [1,1])
schubert_classes(2, G)
```
Notice that `intersection_matrix(X)` contains a lot of redundant information:
intersection numbers that are not in complementary codimensions are always 0.
So usually it is better to separate the components in different codimensions.
## Construct new varieties
See also [Constructors](@ref).
```@docs
*(X::AbsVariety, Y::AbsVariety)
complete_intersection
section_zero_locus
degeneracy_locus
```
### Examples
```@repl repl
proj(1) * proj(1)
complete_intersection(proj(3), 4)
section_zero_locus(OO(proj(3), 4))
X, (A, B) = variety(2, [3=>"a", 4=>"b"]);
D = degeneracy_locus(2, A, B)
pushforward(D → X, D(1))
degeneracy_locus(2, A, B, class=true)
```
