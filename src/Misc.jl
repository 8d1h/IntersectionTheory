###############################################################################
#
# some utility functions
#

function set!(x::fmpz, y::Int)
  ccall((:fmpz_set_si, Nemo.libflint), Nothing, (Ref{fmpz}, Int), x, y)
  return x
end
function set!(x::fmpq, n::fmpz, d::fmpz)
  ccall((:fmpq_set_fmpz_frac, Nemo.libflint), Nothing, (Ref{fmpq}, Ref{fmpz}, Ref{fmpz}), x, n, d)
  return x
end

function _part(n::T, rem::T, k::T, m::T, part::Vector{T}, ans::Vector{Partition{T}}) where T <: Integer
  rem == 0 && (push!(ans, Partition(n, part[1:end-k], false)); return)
  k <= 0 && return
  for v in min(rem, m):-T(1):T(1)
    part[end-k+1] = v
    _part(n, rem-v, k-T(1), v, part, ans)
  end
end
# partitions of n with at most k numbers each <= m
function partitions(n::T, k::T=n, m::T=n) where T <: Integer
  ans = Partition{T}[]
  _part(n, n, k, m, Vector{T}(undef, k), ans)
  return ans
end

# XXX remove once in AA
function combinations(n::Int, k::Int) combinations(1:n, k) end
function combinations(v::AbstractVector{T}, k::Int) where T
  n = length(v)
  ans = Vector{T}[]
  _combinations_dfs!(ans, Vector{T}(undef, k), v, n, k)
  return ans
end
function _combinations_dfs!(ans::Vector{Vector{T}}, comb::Vector{T}, v::AbstractVector{T}, n::Int, k::Int) where T
  k < 1 && (pushfirst!(ans, comb[:]); return)
  for m in n:-1:k
    comb[k] = v[m]
    _combinations_dfs!(ans, comb, v, m - 1, k - 1)
  end
end

function _sym(n::Int, k::Int) _sym(1:n, k) end
function _sym(v::AbstractVector{T}, k::Int) where T
  n = length(v)
  ans = Vector{T}[]
  _sym_dfs!(ans, Vector{T}(undef, k), v, n, k)
  return ans
end
function _sym_dfs!(ans::Vector{Vector{T}}, comb::Vector{T}, v::AbstractVector{T}, n::Int, k::Int) where T
  k < 1 && (pushfirst!(ans, comb[:]); return)
  for m in n:-1:1
    comb[k] = v[m]
    _sym_dfs!(ans, comb, v, m, k - 1)
  end
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

parameters(param::String...) = FunctionField(Singular.QQ, collect(param))[2]

macro parameters(param...)
  :($(esc(Expr(:tuple, param...))) = parameters(string.($param[:])...))
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
(F::Nemo.FmpqMPolyRing)(q::Singular.n_Q) = F(QQ(q))
(F::Nemo.FlintRationalField)(x::Nemo.fmpq_mpoly) = begin
  cst = constant_coefficient(x)
  x == cst || throw(InexactError)
  F(cst)
end
promote_rule(::Type{n_transExt}, ::Type{n_Q}) = Singular.n_transExt
promote_rule(::Type{n_transExt}, ::Type{fmpq}) = Singular.n_transExt

###############################################################################
#
# pretty printing
# 
# generate a list of symbols [x₁,…,xₙ] using LaTeX / unicode for IJulia / REPL
function _parse_symbol(symbol::String, I::AbstractVector)
  isdefined(Main, :IJulia) && Main.IJulia.inited && return [symbol*"_{$i}" for i in I]
  [symbol*subscriptify(i) for i in I]
end
function _parse_symbol(symbol::String, n::Int, I::AbstractVector)
  isdefined(Main, :IJulia) && Main.IJulia.inited && return [symbol*"_{$n,$i}" for i in I]
  [symbol*subscriptify(n)*","*subscriptify(i) for i in I]
end

Base.show(io::IO, x::T) where T <: RingElem =
  print(io, AbstractAlgebra.obj_to_string(x))
Base.show(io::IO, mi::MIME"text/html", x::T) where T <: RingElem =
  print(io, "\$" * AbstractAlgebra.obj_to_latex_string(x) * "\$")
Base.show(io::IO, mi::MIME"text/html", x::T) where T <: Nemo.MatElem =
  print(io, "\$\\left[" * AbstractAlgebra.obj_to_latex_string(x) * "\\right]\$")

function _show_compact(io::IO, mi::MIME"text/html", x)
  try
    show(IOContext(io, :compact => true), mi, x)
  catch e
    if isa(e, MethodError)
      print(io, "<tt>")
      show(IOContext(io, :compact => true), x)
      print(io, "</tt>")
    else
      rethrow(e)
    end
  end
end
function Base.show(io::IO, mi::MIME"text/html", P::Pair)
  if isdefined(Main, :IJulia) && Main.IJulia.inited
    _show_compact(io, mi, P[1])
    print(io, " \$\\Rightarrow\$ ")
    _show_compact(io, mi, P[2])
  else
    show(io, P) 
  end
end
function Base.show(io::IO, mi::MIME"text/html", T::Tuple)
  if isdefined(Main, :IJulia) && Main.IJulia.inited
    print(io, "(")
    sep = false
    for x in T
      if !sep
	sep = true
      else
	print(io, ", ")
      end
      _show_compact(io, mi, x)
    end
    print(io, ")")
  else
    show(io, T) 
  end
end
function Base.show(io::IO, mi::MIME"text/html", V::Vector)
  if isdefined(Main, :IJulia) && Main.IJulia.inited
    space = "&nbsp;&nbsp;"
    if (:compact => true) in io
      print(io, "[")
    else
      print(io, "<pre>$(length(V))-element $(typeof(V)):</pre>$space")
    end
    sep = false
    for x in V
      if !sep
	sep = true
      else
	print(io, (:compact => true) in io ? ",$space" : "<br>$space")
      end
      _show_compact(io, mi, x)
    end
    if (:compact => true) in io
      print(io, "]")
    end
  else
    show(io, V) 
  end
end
function Base.show(io::IO, mi::MIME"text/html", D::Dict)
  if isdefined(Main, :IJulia) && Main.IJulia.inited
    space = "&nbsp;&nbsp;"
    if (:compact => true) in io
      print(io, "{")
    else
      print(io, "<pre>$(typeof(D))")
      if length(D) > 1
	print(io, " with $(length(D)) entries:</pre>$space")
      elseif length(D) == 1
	print(io, " with 1 entry:</pre>$space")
      else
	print(io, "()</pre>")
      end
    end
    sep = false
    for k in sort(collect(keys(D)))
      if !sep
	sep = true
      else
	print(io, (:compact => true) in io ? ",$space" : "<br>$space")
      end
      _show_compact(io, mi, k => D[k])
    end
    if (:compact => true) in io
      print(io, "}")
    end
  else
    show(io, D) 
  end
end
