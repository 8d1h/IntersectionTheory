###############################################################################
#
# some utility functions
#
# polynomial mod, weirdly not found in AbstractAlgebra or Nemo
# this is taken from Hecke
function mod(f::AbstractAlgebra.PolyElem{T}, g::AbstractAlgebra.PolyElem{T}) where {T <: RingElem}
  @assert f.parent == g.parent
  if length(g) == 0
    throw(DivideError())
  end
  if length(f) >= length(g)
    f = deepcopy(f)
    b = leading_coefficient(g)
    g = inv(b)*g
    c = Nemo.base_ring(f)()
    while length(f) >= length(g)
      l = -leading_coefficient(f)
      for i = 1:length(g) 
        c = Nemo.mul!(c, Nemo.coeff(g, i - 1), l)
        u = Nemo.coeff(f, i + length(f) - length(g) - 1)
        u = Nemo.addeq!(u, c)
        f = Nemo.setcoeff!(f, i + length(f) - length(g) - 1, u)
      end
      Nemo.set_length!(f, Nemo.normalise(f, length(f) - 1))
    end
  end
  return f
end

# partitions of n with at most k numbers each ≤ m
function partitions(n::Int, k::Int=n, m::Int=-1)
  ans = Partition[]
  (n > 0 && k == 0) && return ans
  if m < 0 m = n end
  n <= m && push!(ans, Partition(n > 0 ? [n] : Int[]))
  for v in Int(min(n-1,m)):-1:1
    for p in partitions(n-v, k-1, v)
      push!(ans, Partition(pushfirst!(collect(p), v)))
    end
  end
  ans
end

# make combinations work for arrays
function combinations(I::UnitRange, k::Int) combinations(collect(I), k) end
function combinations(l::Vector, k::Int)
  [[l[i] for i in c] for c in combinations(length(l), k)]
end

###############################################################################
#
# coercions
#
(R::Singular.PolyRing)(q::Rational) = R(Singular.QQ(q))
(F::Singular.N_FField)(q::Union{fmpq, Rational, Singular.n_Q}) = F(numerator(q))//F(denominator(q))
(Z::Singular.Integers)(q::Singular.n_Q) = begin
  if denominator(q) != 1 throw(InexactError) end
  Z(numerator(q))
end
(F::Singular.Rationals)(x::Singular.n_transExt) = begin
  num = Singular.n_transExt_to_spoly(Singular.numerator(x))
  cst_num = constant_coefficient(num)
  denom = Singular.n_transExt_to_spoly(Singular.denominator(x))
  cst_denom = constant_coefficient(denom)
  if (num != cst_num || denom != cst_denom) throw(InexactError) end
  F(cst_num)//F(cst_denom)
end
(F::Nemo.FlintRationalField)(x::Singular.n_transExt) = F(Singular.QQ(x))

###############################################################################
#
# pretty printing
# 
# generate a list of symbols [x₁,…,xₙ] using LaTeX / unicode for IJulia / REPL
function _parse_symbol(symbol::String, I::UnitRange)
  isdefined(Main, :IJulia) && Main.IJulia.inited && return [symbol*"_{$i}" for i in I]
  [symbol*subscriptify(i) for i in I]
end
function _parse_symbol(symbol::String, n::Int, I::UnitRange)
  isdefined(Main, :IJulia) && Main.IJulia.inited && return [symbol*"_{$n,$i}" for i in I]
  [symbol*subscriptify(n)*","*subscriptify(i) for i in I]
end

# taken from Hecke
function Base.show(io::IO, mime::MIME"text/html", T::Tuple)
  print(io, "(")
  for i in 1:length(T)
    try
      show(IOContext(io, :compact => true), mime, T[i])
    catch e
      if isa(e, MethodError)
        show(IOContext(io, :compact => true), T[i])
      else
        rethrow(e)
      end
    end
    if i<length(T)
      print(io, ", ")
    end
  end
  print(io, ")")
end
