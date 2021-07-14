Nemo.elem_type(::Type{CobordRing}) = CobordRingElem
Nemo.parent_type(::Type{CobordRingElem}) = CobordRing

Base.parent(x::CobordRingElem) = x.parent
deepcopy(x::CobordRingElem) = parent(x)(deepcopy(x.f))

Base.show(io::IO, R::CobordRing) = print(io, "Cobordism Ring")

(R::CobordRing)(f::Dict{Int, Vector{fmpq}}) = CobordRingElem(R, f)
(R::CobordRing)(n::T) where T <: Union{Int, Rational, fmpz, fmpq} = R(Dict([0 => [QQ(n)]]))
(R::CobordRing)() = R(Dict{Int, Vector{fmpq}}())
zero(R::CobordRing) = R(Dict{Int, Vector{fmpq}}())
one(R::CobordRing) = R(1)
(R::CobordRing)(x::CobordRingElem) = (@assert parent(x) == R; x)
simplify!(x::CobordRingElem) = begin
  for k in keys(x.f)
    if all(iszero, x.f[k]) pop!(x.f, k) end
  end;
  x
end
==(x::CobordRingElem, y::CobordRingElem) = (simplify!(x); simplify!(y); x.f == y.f)
Base.getindex(R::CobordRing, n::Int) = R(Dict([n=>[λ == [n] ? QQ(1) : QQ(0) for λ in partitions(n)]]))
Base.getindex(x::CobordRingElem, n::Int) = n in keys(x.f) ? Omega(Dict([n => x.f[n]])) : Omega()

mul!(c::CobordRingElem, a::CobordRingElem, b::CobordRingElem) = (c.f = (a * b).f; c)
add!(c::CobordRingElem, a::CobordRingElem, b::CobordRingElem) = (c.f = (a + b).f; c)
addeq!(a::CobordRingElem, b::CobordRingElem) = (a.f = (a + b).f; a)

function (R::CobordRing)(X::Variety)
  if X isa AbsVariety
    @assert integral(X(0)) isa fmpq
  end
  CobordRingElem(R, Dict([dim(X) => _to_Pn(X)]))
end

@doc Markdown.doc"""
    cobordism_class(X::Variety)
Construct the cobordism class of a variety $X$."""
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

for T in [:Int, :Rational, :fmpz, :fmpq, :n_Q]
  @eval promote_rule(::Type{CobordRingElem}, ::Type{$T}) = CobordRingElem
end

### ad hoc arithmetics

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

@doc Markdown.doc"""
    chern_numbers(x::CobordRingElem)
    chern_numbers(x::CobordRingElem, P::Vector{<:Partition})
    chern_numbers(x::CobordRingElem; nonzero::Bool)
Compute all the Chern numbers of a cobordism class $[X]$ as a dictionary of
$\lambda\Rightarrow c_\lambda(X)$, or only those corresponding to partitions in
a given vector. Use the argument `nonzero=true` to display only the non-zero
ones.
"""
chern_numbers(x::CobordRingElem)
  
function chern_numbers(x::CobordRingElem, P::Vector{<:Partition}=partitions(dim(x)); nonzero::Bool=false)
  d = dim(x)
  c = _chern_Pn(d)[[i for (i, λ) in enumerate(partitions(d)) if λ in P], :] * Nemo.matrix(QQ, x.f[d][:, :])
  Dict([λ => c[i] for (i, λ) in enumerate(P) if !nonzero || c[i] != 0])
end

function euler(x::CobordRingElem)
  p = Partition([dim(x)])
  chern_numbers(x, [p])[p]
end

@doc Markdown.doc"""
    integral(x::CobordRingElem, t::ChRingElem)
Compute the integral of an expression in terms of the Chern classes over a
cobordism class.
"""
function integral(x::CobordRingElem, t::ChRingElem)
  t = t[dim(x)]
  c = chern_numbers(x)
  f = v -> Partition(vcat([repeat([n], v[n]) for n in length(v):-1:1]...))
  ans = sum(c[f(v)] * (a isa n_Q ? QQ(a) : a) for (a, v) in zip(Nemo.coefficients(t.f), Nemo.exponent_vectors(t.f)) if a != 0)
end

todd(x::CobordRingElem) = integral(x, todd(dim(x)))

function _chern_Pn(n::Int)
  B = get_special(Omega, :basis)
  if B == nothing
    B = Dict{Int, Nemo.fmpq_mat}()
    set_special(Omega, :basis => B)
  end
  if !(n in keys(B))
    P = partitions(n)
    Pn = [proj(k) for k in 1:n]
    c = Dict{Partition, Dict{Partition, fmpq}}()
    for λ in P
      c[λ] = chern_numbers(prod(Pn[d] for d in λ))
    end
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
  coeff(HS, [n])
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
    universal_genus(n::Int; twist::Int=0)
    universal_genus(n::Int, phi::Function; twist::Int=0)
Compute the total class of the universal genus up to degree $n$, possibly with
a twist $t$, in terms of the Chern classes.

One can also compute the total class of an arbitrary genus, by specifying the
images of the projective spaces using a function `phi`.
"""
function universal_genus(n::Int, phi::Function=k -> Omega[k]; twist::Int=0)
  n == 0 && return one(phi(1))
  taylor = _taylor(n, phi)
  R = ChRing(Nemo.PolynomialRing(parent(taylor[1]), _parse_symbol("c", 1:n))[1], collect(1:n), :variety_dim=>n)
  _genus(_logg(sum(gens(R))), taylor, twist = QQ(twist))
end

function _taylor(n::Int, phi::Function=k -> Omega[k])
  F = parent(phi(1))
  n == 0 && return [F(1)]
  ans = _taylor(n-1, phi)
  R = ChRing(Nemo.PolynomialRing(F, ["h"])[1], [1], :variety_dim=>n)
  h = gens(R)[1]
  chTP = sum(ZZ(n+1)//factorial(ZZ(i))*h^i for i in 1:n) # ad hoc ch(proj(n).T)
  ans[n+1] = 1//(n+1)*(phi(n) - coeff(_genus(chTP, push!(ans, F(0))), [n]))
  ans
end

@doc Markdown.doc"""
    generalized_kummer(n::Int)
Construct the cobordism class of a hyperkähler variety of
$\mathrm{Kum}_{n}$-type.
"""
function generalized_kummer(n::Int)
  hilb_S, c₁² = hilb_P2, 9 # one can also use (hilb_P1xP1, 8)
  Rz = ChRing(Nemo.PolynomialRing(Omega, ["z"])[1], [1], :variety_dim=>n+1)
  z = gens(Rz)[1]
  H = [Omega(hilb_S(k)) for k in 1:n+1]
  g = universal_genus(2(n+1), twist=1)
  K = coeff(_logg(sum(integral(H[k], g) * z^k for k in 1:n+1)), [n+1])[2n]
  (-1)^n * QQ(n+1, c₁²) * factorial(ZZ(n+1)) * 2K
end

@doc Markdown.doc"""
    milnor(X::Variety)
Compute the Milnor number $n! \int_X\mathrm{ch}_n(T_X)$ of a variety $X$.
"""
milnor(X::Variety) = factorial(ZZ(dim(X))) * integral(ch(X.T))
milnor(x::CobordRingElem) = factorial(ZZ(dim(x))) * integral(x, ch(variety(dim(x)).T))

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
