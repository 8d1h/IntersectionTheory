# IntersectionTheory
[![](https://img.shields.io/badge/docs-latest-blue.svg)](https://8d1h.github.io/IntersectionTheory/dev/)

*IntersectionTheory* is an early stage Julia package for doing computations in intersection theory, built using the components of [Oscar](https://oscar.computeralgebra.de/) ([Nemo](https://nemocas.org/), [Singular.jl](https://github.com/oscar-system/Singular.jl), and [GAP.jl](https://github.com/oscar-system/GAP.jl)).

It's heavily inspired by the Macaulay2 package [*Schubert2*](https://faculty.math.illinois.edu/Macaulay2/doc/Macaulay2/share/doc/Macaulay2/Schubert2/html/) and the Sage library [*Chow*](https://www.math.sciences.univ-nantes.fr/~sorger/en/chow/). Some functionalities from [*Schubert3*](https://github.com/hiepdang/Sage) are also implemented. Compared to these, the advantage is the vast improvement in performance due to the efficiency of Julia and Oscar.

## Installation
Hopefully this will be shipped with Oscar in the future. Right now it can be
installed as follows.
```julia-repl
julia> using Pkg
julia> Pkg.add(url="https://github.com/8d1h/IntersectionTheory")
```

To use it, type the following and wait for the package to load.
```julia-repl
julia> using IntersectionTheory
```

## Some examples
```julia-repl
julia> chern(proj(4))
1 + 5*h + 10*h^2 + 10*h^3 + 5*h^4

julia> todd(2)
1//12*c₁^2 + 1//12*c₂

julia> C, d = curve("g", param="d")
(AbsVariety of dim 1, d)

julia> chi(OO(C, d*C.point))
-g + d + 1

julia> B = blowup_points(2, proj(2))
AbsVariety of dim 2

julia> canonical_class(B)
e₂ + e₁ - 3*h

julia> intersection_matrix(basis(1, B))
[1    0    0]
[0   -1    0]
[0    0   -1]

julia> S = complete_intersection(proj(3), 4)
AbsVariety of dim 2

julia> hilbert_polynomial(S)
2*t^2 + 2

julia> signature(S)
-16

julia> integral(ctop(symmetric_power(3, dual(bundles(grassmannian(2, 4))[1]))))
27
```

## Functionalities
- `ChRing` and `ChRingElem` for handling graded rings with weights, and their quotients;
- Basic constructions for doing intersection theory, including `AbsVariety` represented by the Chow ring, `AbsBundle` represented by Chern characters, `AbsVarietyHom` for morphisms, and various operators that can be used on them;
- Blowing up subvarieties;
- Constructors for projective spaces, Grassmannians, flag varieties, and their relative versions;
- Constructors for moduli spaces of matrices, and parameter spaces of twisted cubics;
- Some basic functionalities for computing integrals using Bott's formula, including `TnVariety` for varieties with a torus action, and `TnBundle` for equivariant bundles;
- Constructors for Grassmannians and flag varieties as `TnVariety`.
