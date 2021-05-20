module IntersectionTheory

import AbstractAlgebra
import Nemo
import Singular
import Markdown

import Base: +, -, *, ^, ==, div, zero, one, parent, mod
import Nemo: fmpz, fmpq, ZZ, QQ
import Nemo: dim, rank, domain, codomain, gens, inv, det, basis, bernoulli
import Nemo: Ring, RingElem, MPolyRing, mul!, addeq!
import Nemo: leading_coefficient, total_degree, ishomogeneous, base_ring, constant_coefficient
import Nemo: map_from_func
import AbstractAlgebra.Generic: Partition, subscriptify, combinations, integral, partitions, FunctionalMap
import AbstractAlgebra: @declare_other, set_special, get_special
import Singular: PolynomialRing, Ideal, FunctionField
import Singular: std, betti, sideal, n_Q, n_transExt, spoly
import Singular: ordering_dp, ordering_wp

export Nemo, Singular
export QQ, FunctionField, PolynomialRing # QQ is Nemo.QQ
export total_degree, ishomogeneous
export proj, grassmannian, flag, point, variety, bundle
export pullback, pushforward, hom
export bundles, tangent_bundle, cotangent_bundle, canonical_bundle, canonical_class
export exterior_power, symmetric_power, det, schur_functor
export dim, degree, rank, basis, intersection_matrix, dual_basis
export simplify, simplify!, inv, gens, domain, codomain, betti
export euler, todd, integral, chern, segre, chi, OO, dual, ch, ctop, pontryagin
export chern_number, chern_numbers, l_genus, a_hat_genus, signature
export hilbert_polynomial #, todd_polynomial
export section_zero_locus, complete_intersection, degeneracy_locus
export schubert_class, schubert_classes
export →
export blowup, blowup_points
export trim!
export twisted_cubics, matrix_moduli

include("Types.jl")
include("Misc.jl")

include("Bott.jl")   # integration using Bott's formula
include("Main.jl")   # basic constructions for Schubert calculus
include("Blowup.jl") # blowup
include("Moduli.jl") # moduli of matrices, twisted cubics

end
