module Test
using Oscar
import Nemo.AbstractAlgebra: set_special, get_special
export grassmannian

function _logg(x::RingElem)
  A = parent(x)
  n = get_special(A, :variety_dim)
  p = repeat([A()], n+1)
  @time comps = homogenous_components(x)
  Z = A.R.D
  e = [(Z([i]) in keys(comps) ? A(comps[Z([i])]) : A()) for i in 0:n]
  for i in 1:n
    p[i+1] = -ZZ(i)*e[i+1] - sum([e[j+1] * p[i-j+1] for j in 1:i-1], init=A())
  end
  simplify(sum([(-1)^i//factorial(ZZ(i))*p[i+1] for i in 1:n], init=A()))
end

function grassmannian(k::Int, n::Int)
  @assert k < n
  R = filtrate(PolynomialRing(QQ, ["c$i" for i in 1:k])[1], collect(1:k))
  c = gens(R)
  Z = R.D
  ic = sum((-sum(c))^i for i in 1:n) # since c(S)⋅c(Q) = 1, this gives c(Q)
  @time comps = homogenous_components(ic)
  I = ideal([comps[Z([i])] for i in n-k+1:n]) # conditions given by rank(Q) = n-k
  A, toA = quo(R, I) # A is the Chow ring of Gr(k, n)
  set_special(A, :variety_dim => k*(n-k))
  # compute the Chern character of the tautological subbundle
  k + _logg(1 + sum(gens(A)))
end

end # module
using .Test
