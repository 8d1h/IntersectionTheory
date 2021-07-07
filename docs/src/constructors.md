```@meta
CurrentModule = IntersectionTheory
DocTestSetup = quote
  using IntersectionTheory
end
```
```@setup repl
using IntersectionTheory
```
# Constructors
## Generic varieties
The following constructors are available for building generic varieties.
```@docs
variety
point
curve
```
### Examples
```@repl repl
X, (h, c1, c2) = variety(2, ["h", "c1", "c2"], [1, 1, 2])
Y, (E,) = variety(2, [3 => "c"])
chern(E)
Z = variety(2)
chern(tangent_bundle(Z))
point()
curve(3)
euler(curve("g"))
```
For all the above constructors, one can use the `param` argument to introduce
parameters. Basically, this will change the coefficient ring of the Chow ring
to a Singular's `FunctionField`. One can also directly pass the function field
using the `base` argument.
```@repl repl
C, d = curve("g", param="d")
chi(OO(C, d*C.point))
S, (E,), d = variety(2, [2 => "c"], param="d")
chern(d*E)
F = base_ring(S)
X = variety(3, base=F)
d*OO(X)
```
!!! note
    The generic varieties are created without any relations by default. There
    are of course trivial relations due to dimension (i.e., all classes with
    codimension larger than the dimension of the variety must be zero). Use
    `trim!` on the Chow ring will add these relations and make the quotient
    ring Artinian. Then we will be able to compute `basis`, `betti`, and
    related things.

## Projective spaces, Grassmannians, flag varieties
The following constructors are available.

```@docs
proj(n::Int)
grassmannian(k::Int, n::Int; bott::Bool=false)
flag(dims::Int...; bott::Bool=false)
```
!!! note
    Mathematically $\mathrm{Fl}(k, n)$ is exactly the same as $\mathrm{Gr}(k,
    n)$. The difference is that the Chow ring returned by `grassmannian` uses
    only $k$ generators instead of $n$.

### Examples
```@repl repl
proj(2)
grassmannian(2, 4)
grassmannian(2, 4, bott=true)
flag(1, 3, 5)
flag([1, 3, 5])
```
Again one can use the `param` and `base` arguments to introduce parameters.
```@repl repl
P2, d = proj(2, param="d");
chern(OO(P2, d))
1 - euler(complete_intersection(P2, d))//2
symmetric_power(d, 2OO(P2))
```

## Projective bundles, relative flag varieties
In the relative setting, the following constructors are available.
```@docs
proj(F::AbsBundle)
flag(d::Int, F::AbsBundle)
```

## Moduli spaces of matrices, parameter spaces of twisted cubics
```@docs
matrix_moduli
twisted_cubics
twisted_cubics_on_quintic_threefold
twisted_cubics_on_cubic_fourfold
```
!!! warning
    The various `twisted_cubics` functions produce the same result as *Chow*,
    however I cannot reproduce the intersection numbers found by Schubert.
    More investigation is needed.
### Examples
A general degree-30 K3 surface can be realized as a zero locus on $N(4;2,3)$,
by results of Mukai.
```@repl repl
X = matrix_moduli(4,2,3)
S = section_zero_locus(2dual(sum(bundles(X))))
chi(OO(S)), euler(S), chern(1, S) # the numerical invariants of a K3 surface
S.O1 = -basis(1, S)[1]; degree(S)
```

## Others
```@docs
linear_subspaces_on_hypersurface
```
### Examples
```@repl repl
IntersectionTheory.linear_subspaces_on_hypersurface(1, 3)
```

