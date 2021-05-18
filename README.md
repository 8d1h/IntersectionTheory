# IntersectionTheory
[![](https://img.shields.io/badge/docs-blue.svg)](https://8d1h.github.io/IntersectionTheory/dev/)

*IntersectionTheory* is a Julia package for doing computations in intersection theory, built on top of [Nemo](https://nemocas.org/) and [Singular.jl](https://github.com/oscar-system/Singular.jl).

It's heavily inspired by the Macaulay2 package [*Schubert2*](https://faculty.math.illinois.edu/Macaulay2/doc/Macaulay2/share/doc/Macaulay2/Schubert2/html/) and the Sage library [*Chow*](https://www.math.sciences.univ-nantes.fr/~sorger/en/chow/). Some functionalities from [*Schubert3*](https://github.com/hiepdang/Sage) are also implemented. Compared to these, the advantage is the vast improvement in performance due to the efficiency of Julia, Nemo, and Singular.

## Installation
Hopefully this will be shipped with [Oscar](https://oscar.computeralgebra.de/)
in the future. Right now it can be installed as follows.
```julia-repl
julia> using Pkg
julia> Pkg.add(url="https://github.com/8d1h/IntersectionTheory")
```

## Functionalities
- `ChRing` and `ChRingElem` for handling graded rings with weights, and their quotients;
- Basic constructions for doing intersection theory, including `AbsVariety` represented by the Chow ring, `AbsBundle` represented by Chern characters, `AbsVarietyHom` for morphisms, and various operators that can be used on them;
- Blowing up subvarieties;
- Constructors for projective spaces, Grassmannians, flag varieties, and their relative versions;
- Constructors for moduli spaces of matrices, and parameter spaces of twisted cubics;
- Some basic functionalities for computing integrals using Bott's formula, including `TnVariety` for varieties with a torus action, and `TnBundle` for equivariant bundles;
- Constructors for Grassmannians and flag varieties as `TnVariety`.
