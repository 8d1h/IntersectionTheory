###############################################################################
#
# some utility functions
#

# XXX division for n_unknown{Nemo.FieldElem}
# remove once this is in Singular.jl
function div(x::Singular.spoly{T}, y::Singular.spoly{T}) where T <: Singular.n_unknown{S} where S <: Nemo.FieldElem
   Singular.check_parent(x, y)
   R = parent(x)
   GC.@preserve x y R begin
      px = Singular.libSingular.p_Copy(x.ptr, R.ptr)
      py = Singular.libSingular.p_Copy(y.ptr, R.ptr)
      q = R(Singular.libSingular.p_Divide(px, py, R.ptr))
      Singular.libSingular.check_error()
      return q
   end
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

# construct appropriate base field
function _parse_base(base::Ring, param::Union{String, Vector{String}})
  p = Singular.n_transExt[]
  if base == QQ || base == Singular.QQ
    if base == QQ base = Singular.QQ end
    if param isa String
      base, (p,) = FunctionField(Singular.QQ, [param])
    elseif param != []
      base, p = FunctionField(Singular.QQ, param)
    end
  else
    param == [] || error("incorrect specification for parameters")
  end
  return base, p
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
promote_rule(::Type{spoly{T}}, ::Type{fmpq}) where T <: RingElem = spoly{T}

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
