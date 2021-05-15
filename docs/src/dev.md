```@meta
CurrentModule = IntersectionTheory
DocTestSetup = quote
  using IntersectionTheory
end
```
```@setup repl
using IntersectionTheory
```
# Development notes

## Comparisons with other packages
This package is largely a translation of existing functionalities from
*Schubert2*, *Chow*, and *Schubert3* into Julia. Since most of the
functionalities are already available elsewhere, the improvement in performance
is important to justify its existence.

### *Schubert2*
For *Schubert2*, we have already covered most of the functionalities, with the
following exceptions:
- Isotropic flag bundles;
- `Correspondence` and `IncidenceCorrespondence` (what are the use cases for these?);
- Better support for Schubert classes.
- 

Polynomial arithmetics in *Macaulay2* are quite slow compared to *Nemo* and
*Singular*. So most computations will automatically run a lot faster in this
package than *Schubert2*.

### *Chow*
For *Chow*, (almost?) all functionalities are covered, notably the construction
of parameter spaces for twisted cubics, which is one of its key features.
Moreover, we implemented constructors for moduli spaces of matrices with
arbitrary size.

Most computations in this package should run faster with a constant factor of 2
to 5 when compared to *Chow*, thanks to the high efficiency of the Julia/Oscar
combo. Note that the blowup procedure in *Chow* is particularly inefficient.
See below for comparisons.

### *Schubert3*
For *Schubert3*, we implemented the functionality of computing integrals using
Bott's formula on Grassmannians, and on flag varieties in general. Moduli
spaces of maps (Kontsevich's spaces) are not implemented yet.

Again, most computations in this package should run faster with a constant
factor.

### Others
A large part of the *Singular* library *chern.lib* is also covered.

## Benchmarks
All the timings are done on an Intel(R) Core(TM) i5-8350U CPU @ 1.70GHz.
### Computing Todd class
```julia-repl
julia> @time todd(proj(200));
  0.353537 seconds (989.07 k allocations: 44.766 MiB, 4.73% gc time)
```
*Chow*:
```
sage: time t = Proj(200).tangent_bundle().todd_class();
CPU times: user 1.23 s, sys: 715 µs, total: 1.23 s
Wall time: 1.19 s
```
*Schubert3*:
```
sage: time t = ProjectiveSpace(200).tangent_bundle().todd_class();
CPU times: user 2.15 s, sys: 1.15 ms, total: 2.15 s
Wall time: 2.15 s
```
*Schubert2* and *chern.lib* are far slower so are not included.

### Computing blowup
The computation of the blowup requires a "pushforward" function. In *Macaulay2*
there are two implementations: `pushForward`, and `pushFwd` from the
*PushForward* package. The former appears to be faster so we followed this
implementation. (Our implementation is still not optimal and is slower than
*Macaulay2*'s.)

On the other hand, the counterpart in *Chow*, `FiniteRingExtension`, is very
inefficient. This makes blowups in *Chow* very slow.

We compute the blowup of $\mathbf P^{20}$ at a point.
```julia-repl
julia> @time blowup(point() → proj(20))[1] |> euler
  0.011019 seconds (60.98 k allocations: 1.391 MiB)
40
```
*Schubert2*:
```
i12 : p = abstractProjectiveSpace 0; time euler first blowup map(abstractProjectiveSpace 20, p, OO_p)
     -- used 1.09486 seconds

o13 = 40
```
*Chow*:
```
sage: time Blowup(PointChowScheme.hom("0", Proj(20))).codomain().euler_number()
CPU times: user 16.7 s, sys: 6.9 ms, total: 16.7 s
Wall time: 16.8 s
40
```
*Schubert3* does not seem to provide this functionality.

Since the computations related to parameter spaces of twisted cubics use
blowup, they run significantly faster in this package than with *Chow*.
- Compute the number of twisted cubics on a quintic threefold
  `twisted_cubics_on_quintic_threefold`: 5s v.s. 1min;
- Compute the Euler number of the LLSvS eightfold
  `twisted_cubics_on_cubic_fourfold`: 2min v.s. 20min.

### Linear subspaces on hypersurfaces
#### Using Schubert calculus
```julia-repl
julia> @time IntersectionTheory.linear_subspaces_on_hypersurface(1, 35, bott=false)
  0.257564 seconds (1.66 M allocations: 30.382 MiB)
513687287764790207960329434065844597978401438841796875

julia> @time IntersectionTheory.linear_subspaces_on_hypersurface(2, 7, bott=false)
  0.430082 seconds (2.68 M allocations: 42.083 MiB, 1.66% gc time)
279101475496912988004267637
```
*Schubert2*:
```
i4 : time integral chern symmetricPower_35 dual first bundles flagBundle{2,18}
     -- used 15.2021 seconds

o4 = 513687287764790207960329434065844597978401438841796875

i5 : time integral chern symmetricPower_7 dual first bundles flagBundle{3,12}
     -- used 12.3326 seconds

o5 = 279101475496912988004267637
```
*Chow*:
```
sage: time Grass(2,20).sheaves['universal_sub'].dual().symm(35).chern_classes()[-1].integral()
CPU times: user 787 ms, sys: 12.6 ms, total: 800 ms
Wall time: 812 ms
513687287764790207960329434065844597978401438841796875

sage: time Grass(3,15).sheaves['universal_sub'].dual().symm(7).chern_classes()[-1].integral()
CPU times: user 1.99 s, sys: 19.4 ms, total: 2.01 s
Wall time: 2.02 s
279101475496912988004267637
```
*Schubert3* is much slower and is not included.

#### Using Bott's formula
```julia-repl
julia> @time IntersectionTheory.linear_subspaces_on_hypersurface(1, 57)
  0.263851 seconds (2.17 M allocations: 70.302 MiB, 36.51% gc time)
4543008461967180205447462399408892034555800983810817102531043233080341547902307166123135185210701405

julia> @time IntersectionTheory.linear_subspaces_on_hypersurface(3, 5)
  0.546194 seconds (4.84 M allocations: 236.776 MiB, 31.41% gc time)
64127725294951805931404297113125
```
*Schubert3* is slightly a bit faster when $k=1$, but slower with bigger $k$.
```
sage: time linear_subspaces_hypersurface(1,57,30)
CPU times: user 260 ms, sys: 0 ns, total: 260 ms
Wall time: 260 ms
4543008461967180205447462399408892034555800983810817102531043233080341547902307166123135185210701405

sage: time linear_subspaces_hypersurface(3,5,17)
CPU times: user 2.15 s, sys: 0 ns, total: 2.15 s
Wall time: 2.15 s
64127725294951805931404297113125
```

## Some notes

### Quotient rings
In a quotient ring, when should we do the reductions? It is obviously very
costly to do this frequently; on the other hand, if we don't do it at all, we
may accumulate some super complicated elements that will take a long time to
reduce in the end. I find a good balance point is to do reduction for
multiplications and powers, but not for additions and substractions. Here are
some timings for a comparison. The bottleneck is when computing the Chern
characters for the tautological subbundles using their Chern classes.

Current solution (reduction for `*` and `^` only)
```julia-repl
julia> @time flag(3,6,9);
  0.045371 seconds (489.13 k allocations: 6.366 MiB)
```
Reduction for all the operators
```julia-repl
julia> @time flag(3,6,9);
  0.161490 seconds (769.00 k allocations: 8.604 MiB)
```
No reduction at all
```julia-repl
julia> @time flag(3,6,9);
  1.168490 seconds (8.57 M allocations: 124.392 MiB, 1.07% gc time)
```

(Although this necessarily means that the ideal should be in a standard basis.)

### Notes on Chow rings
- For a given `AbsVariety`, the underlying Singular ring of the Chow ring
  should *never* be modified: otherwise bundles already constructed will no longer
  be compatible. So whenever a new Singular ring is used, a new instance of
  `AbsVariety` should be created (e.g. `_inclusion`).

- On the other hand, the ideal could be changed but one should be careful. In
  particular, since `basis_by_degree` is cached (this is necessary due to
  performance reasons, since we need to check the number of zero cycles when
  doing integration), changing the ideal may lead to issues. But `trim!` is an
  exception since it does not change the structure and is in fact needed before
  performing `basis_by_degree` (otherwise the ideal might not be 0-dimensional
  and we won't be able to use `kbase`).
