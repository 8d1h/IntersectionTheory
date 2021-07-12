
Nemo.elem_type(::Type{CobordRing}) = CobordRingElem
Nemo.parent_type(::Type{CobordRingElem}) = CobordRing

Base.parent(x::CobordRingElem) = x.parent
deepcopy(x::CobordRingElem) = parent(x)(deepcopy(x.f))

const Omega = CobordRing(Dict{Symbol, Any}())

Base.show(io::IO, R::CobordRing) = print(io, "Cobordism Ring")

(R::CobordRing)(f::Dict{Int, Vector{fmpq}}) = CobordRingElem(R, f)
(R::CobordRing)(n::T) where T <: Union{Int, Rational, fmpz, fmpq} = R(Dict([0 => [QQ(n)]]))
(R::CobordRing)() = R(Dict{Int, Vector{fmpq}}())
zero(R::CobordRing) = R(Dict{Int, Vector{fmpq}}())
one(R::CobordRing) = R(1)
(R::CobordRing)(x::CobordRingElem) = (@assert parent(x) == R; x)
==(x::CobordRingElem, y::CobordRingElem) = x.f == y.f
Base.getindex(R::CobordRing, n::Int) = R(Dict([n=>[λ == [n] ? QQ(1) : QQ(0) for λ in partitions(n)]]))

mul!(c::CobordRingElem, a::CobordRingElem, b::CobordRingElem) = (c.f = (a * b).f; c)
add!(c::CobordRingElem, a::CobordRingElem, b::CobordRingElem) = (c.f = (a + b).f; c)
addeq!(a::CobordRingElem, b::CobordRingElem) = (a.f = (a + b).f; a)

function (R::CobordRing)(X::Variety)
  if X isa AbsVariety
    @assert integral(X(0)) isa fmpq
  end
  CobordRingElem(R, Dict([dim(X) => _to_Pn(X)]))
end
cobordism_class(X::Variety) = Omega(X)

function (R::CobordRing)(c::Dict{T, fmpq}) where T <: Partition
  P = collect(keys(c))
  n = sum(P[1])
  @assert all(x -> sum(x) == n, P)
  CobordRingElem(R, Dict([n => _to_Pn(n, c)]))
end

function expressify(x::CobordRingElem; context = nothing)
  ans = Expr(:call, :+)
  for d in sort(collect(keys(x.f)))
    if d == 0 && x.f[d][1] != 0
      push!(ans.args, expressify(x.f[d][1], context = context))
    elseif d > 0
      P = partitions(d)
      for (c, p) in zip(x.f[d], P)
	if !iszero(c)
	  push!(ans.args, Expr(:call, :*, expressify(c, context = context), "[$(_print_Pn(p))]"))
	end
      end
    end
  end
  ans
end

Base.show(io::IO, x::CobordRingElem) =
  print(io, AbstractAlgebra.obj_to_string(x))

function _print_Pn(p::Partition)
  join(["P$i" for i in p], "x")
end

### ad hoc arithmetics

for T in [:Int, :Rational, :fmpz, :fmpq, :n_Q]
  @eval function *(x::CobordRingElem, a::$T)
    ans = deepcopy(x)
    for d in keys(ans.f)
      ans.f[d] .*= a
    end
    ans
  end
  @eval function *(a::$T, x::CobordRingElem)
    x * a
  end
end

function +(x::CobordRingElem, y::CobordRingElem)
  ds = union(keys(x.f), keys(y.f))
  ans = parent(x)()
  for d in ds
    fd = sum(f[d] for f in [x.f, y.f] if d in keys(f))
    if !all(iszero, fd)
      ans.f[d] = fd
    end
  end
  ans
end

function -(x::CobordRingElem)
  ans = parent(x)()
  for d in keys(x.f)
    ans.f[d] = -x.f[d]
  end
  ans
end

function -(x::CobordRingElem, y::CobordRingElem)
  x + -y
end

function *(x::CobordRingElem, y::CobordRingElem)
  ans = parent(x)()
  for d in keys(x.f)
    Pd = partitions(d)
    for e in keys(y.f)
      Pe = partitions(e)
      Pde = partitions(d+e)
      fde = Dict([p => QQ() for p in Pde])
      for (a, p) in zip(x.f[d], Pd)
	for (b, q) in zip(y.f[e], Pe)
	  fde[Partition(sort(vcat(p, q), rev=true))] += a*b
	end
      end
      fde = [fde[λ] for λ in Pde]
      if d+e in keys(ans.f)
	ans.f[d+e] += fde
      else
	ans.f[d+e] = fde
      end
    end
  end
  ans
end

function ^(x::CobordRingElem, n::Int)
  n == 0 && return one(parent(x))
  prod(repeat([x], n))
end

function dim(x::CobordRingElem)
  ds = collect(keys(x.f))
  length(ds) == 1 || error("the element is not equidimensional")
  ds[1]
end

function chern_numbers(x::CobordRingElem, P::Vector{T}=partitions(dim(x)); nontriv::Bool=false) where T <: Partition
  d = dim(x)
  c = _chern_Pn(d)[[i for (i, λ) in enumerate(partitions(d)) if λ in P], :] * Nemo.matrix(QQ, x.f[d][:, :])
  Dict([λ => c[i] for (i, λ) in enumerate(P) if !nontriv || c[i] != 0])
end

function euler(x::CobordRingElem)
  p = Partition([dim(x)])
  chern_numbers(x, [p])[p]
end

function integral(x::CobordRingElem, t::ChRingElem)
  t = t[dim(x)]
  c = chern_numbers(x)
  f = v -> Partition(vcat([repeat([n], v[n]) for n in length(v):-1:1]...))
  ans = sum(c[f(v)] * a for (a, v) in zip(Nemo.coeffs(t.f), Nemo.exponent_vectors(t.f)) if a != 0)
  # convert ans to fmpq in case that we get a Singular n_Q
  ans isa n_Q ? QQ(ans) : ans
end

function _chern_Pn(n::Int)
  B = get_special(Omega, :basis)
  if B == nothing
    B = Dict{Int, Nemo.fmpq_mat}()
    set_special(Omega, :basis => B)
  end
  if !(n in keys(B))
    P = partitions(n)
    Pn = [proj(k) for k in 1:n]
    c = Dict([λ => chern_numbers(prod(Pn[d] for d in λ)) for λ in P])
    B[n] = Nemo.matrix(QQ, [c[μ][λ] for λ in P, μ in P])
  end
  B[n]
end

function _to_Pn(X::Variety)
  _to_Pn(dim(X), chern_numbers(X))
end

function _to_Pn(n::Int, c::Dict{T, fmpq}) where T <: Partition
  c = [λ in keys(c) ? c[λ] : QQ() for λ in partitions(n), j in 1:1]
  vec(collect(Nemo.solve(_chern_Pn(n), Nemo.matrix(QQ, c))))
end

# Ellingsrud-Göttsche-Lehn
# On the cobordism class of the Hilbert scheme of a surface
@doc Markdown.doc"""
    hilb_surface(n::Int, c1_2::Int, c2::Int)
Construct the cobordism class of the Hilbert scheme of $n$ points on a surface
with given Chern numbers $c_1^2$ and $c_2$.
"""
function hilb_surface(n::Int, c1_2::Int, c2::Int)
  HS = _H(n, c1_2, c2)
  collect(Nemo.coeffs(HS[n].f))[1]
end

@doc Markdown.doc"""
    hilb_K3(n::Int)
Construct the cobordism class of a hyperkähler variety of
$\mathrm{K3}^{[n]}$-type.
"""
function hilb_K3(n)
  hilb_surface(n, 0, 24)
end

# the generating series H(S) for a surface S
function _H(n::Int, c1_2::Int, c2::Int)
  a1, a2 = Nemo.solve(Nemo.matrix(QQ, [9 3; 8 4]'), Nemo.matrix(QQ, [c1_2 c2]'))
  S, (z,) = Nemo.PolynomialRing(Omega, ["z"])
  R = ChRing(S, [1], :variety_dim => n)
  HP2    = a1 == 0 ? R() : 1 + R(sum(Omega(hilb_P2(k))*z^k for k in 1:n))
  HP1xP1 = a2 == 0 ? R() : 1 + R(sum(Omega(hilb_P1xP1(k))*z^k for k in 1:n))
  _expp(a1*_logg(HP2) + a2*_logg(HP1xP1))
end

@doc Markdown.doc"""
    universal_genus(n::Int)
    universal_genus(n::Int, t::Int)
Compute the total class of the universal genus up to degree $n$, possibly with
a twist $t$, in terms of the Chern classes."""
function universal_genus(n::Int, t::Int=0)
  n == 0 && return Omega(1)
  R = ChRing(Nemo.PolynomialRing(Omega, _parse_symbol("c", 1:n))[1], collect(1:n), :variety_dim=>n)
  _genus(_logg(sum(gens(R))), _taylor(n), twist = QQ(t))
end

# XXX this needs to be improved!
function _taylor(n::Int)
  T = get_special(Omega, :taylor)
  if T == nothing
    T = Dict{Int, CobordRingElem}([0 => Omega(1)])
    set_special(Omega, :taylor => T)
  end
  if !(n in keys(T))
    if n == 1
      T[1] = 1//2*Omega[1]
    else
      R = ChRing(Nemo.PolynomialRing(Omega, _parse_symbol("c", 1:n))[1], collect(1:n), :variety_dim=>n)
      T[n] = 1//(n+1)*(Omega[n] - integral(Omega[n], _genus(_logg(sum(gens(R))), push!(_taylor(n-1), Omega(0)))))
    end
  end
  [T[k] for k in 0:n]
end

@doc Markdown.doc"""
    generalized_kummer(n::Int)
Construct the cobordism class of a hyperkähler variety of
$\mathrm{Kum}_{n}$-type.
"""
function generalized_kummer(n::Int)
  n += 1
  Rz = ChRing(Nemo.PolynomialRing(Omega, ["z"])[1], [1], :variety_dim=>n)
  z = gens(Rz)[1]
  H = [Omega(hilb_P2(k)) for k in 1:n]
  K1 = collect(Nemo.coeffs(_logg(sum(integral(H[k], universal_genus(2k, 1)) * z^k for k in 1:n))[n].f))[1]
  # avoid computing id_{-1}, by simply removing the odd-degree terms
  K1 = Omega(Dict([λ => K1.f[λ] for λ in keys(K1.f) if iseven(sum(λ))]))
  K = K1 - collect(Nemo.coeffs(_logg(sum(H[k] * z^k for k in 1:n))[n].f))[1]
  n//9 * (-1)^(n-1) * factorial(n) * 2K
end

function OG6()
  Omega(
    Dict([Partition([2,2,2]) => QQ(30720),
	  Partition([4,2])   => QQ(7680),
	  Partition([6])     => QQ(1920)
	 ]))
end

function OG10()
  Omega(
    Dict([Partition([2,2,2,2,2]) => QQ(127370880),
	  Partition([4,2,2,2])   => QQ(53071200),
	  Partition([6,2,2])     => QQ(12383280),
	  Partition([8,2])       => QQ(1791720),
	  Partition([4,4,2])     => QQ(22113000),
	  Partition([6,4])       => QQ(5159700),
	  Partition([10])        => QQ(176904)
	 ]))
end

# not feasible at the moment...
function Kum7()
  Omega(
    Dict([Partition([2,2,2,2,2,2,2]) => QQ(421414305792),
	  Partition([4,2,2,2,2,2])   => QQ(149664301056),
	  Partition([4,4,2,2,2])     => QQ(53149827072),
	  Partition([4,4,4,2])       => QQ(18874417152),
	  Partition([6,2,2,2,2])     => QQ(24230756352),
	  Partition([6,4,2,2])       => QQ(8610545664),
	  Partition([6,4,4])         => QQ(3059945472),
	  Partition([6,6,2])         => QQ(1397121024),
	  Partition([8,2,2,2])       => QQ(1914077184),
	  Partition([8,4,2])         => QQ(681332736),
	  Partition([8,6])           => QQ(110853120),
	  Partition([10,2,2])        => QQ(71909376),
	  Partition([10,4])          => QQ(25700352),
	  Partition([12,2])          => QQ(1198080),
	  Partition([14])            => QQ(7680)
	 ]))
end
