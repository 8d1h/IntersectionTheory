module IntersectionTheory

import AbstractAlgebra
import Nemo
import Singular

import Base: +, -, *, ^, ==, div, zero, one, parent, mod
import Nemo: fmpz, fmpq, ZZ, QQ
import Nemo: dim, rank, domain, codomain, gens, inv, det, basis, bernoulli
import Nemo: Ring, RingElem, MPolyRing, mul!, addeq!
import Nemo: leading_coefficient, total_degree, base_ring, constant_coefficient
import Nemo: map_from_func
import AbstractAlgebra.Generic: Partition, subscriptify, combinations, integral, partitions, FunctionalMap
import AbstractAlgebra: @declare_other, set_special, get_special
import Singular: PolynomialRing, Ideal, FunctionField
import Singular: std, betti, sideal, n_Q, n_transExt

export Nemo, Singular
export QQ, FunctionField # QQ is Nemo.QQ
export proj, grassmannian, flag, point, variety, sheaf
export pullback, pushforward, hom
export tangent_bundle, cotangent_bundle, canonical_bundle, canonical_class
export exterior_power, symmetric_power, det, schur_functor
export dim, degree, rank, basis, basis_by_degree, intersection_matrix
export simplify, inv, gens, domain, codomain, betti
export euler, todd, integral, chern, segre, chi, OO, dual, ch, ctop
export chern_number, chern_numbers, l_genus, a_hat_genus, signature
export hilbert_polynomial #, todd_polynomial
export section_zero_locus, complete_intersection, degeneracy_locus
export schubert_class, schubert_classes
export →
export blowup

include("Types.jl")
include("Misc.jl")

include("Bott.jl")   # integration using Bott's formula
include("Main.jl")   # basic constructions for Schubert calculus
include("Blowup.jl") # blowup

end
