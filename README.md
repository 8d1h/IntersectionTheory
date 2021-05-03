# IntersectionTheory

Julia package for doing computations in intersection theory. Built on top of [Nemo](https://nemocas.org/) and [Singular.jl](https://github.com/oscar-system/Singular.jl).

Heavily inspired by the Macaulay2 package [*Schubert2*](https://faculty.math.illinois.edu/Macaulay2/doc/Macaulay2/share/doc/Macaulay2/Schubert2/html/) and the Sage library [*Chow*](https://www.math.sciences.univ-nantes.fr/~sorger/en/chow/). Some functionalities from [*Schubert3*](https://github.com/hiepdang/Sage) are also implemented. Compared to these, the advantage is the vast improvement in performance due to the efficiency of Julia, Nemo, and Singular.

Functionalities implemented

- `ChRing` and `ChRingElem` for handling graded rings with weights, and their quotients;
- Basic constructions for doing intersection theory, including `AbsVariety` represented by the Chow ring, `AbsSheaf` represented by Chern characters, `AbsVarietyHom` for morphisms, and various operators that can be used on them;
- Blowing up subvarieties;
- Constructors for projective spaces, Grassmannians, flag varieties, and their relative versions;
- Some basic functionalities for computing integrals using Bott's formula, including `TnVariety` for varieties with a torus action, and `TnBundle` for equivariant bundles;
- Constructors for Grassmannians and flag varieties as `TnVariety`.
