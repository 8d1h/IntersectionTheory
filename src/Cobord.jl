Nemo.elem_type(::Type{CobordRing}) = CobordRingElem
Nemo.parent_type(::Type{CobordRingElem}) = CobordRing

Base.parent(x::CobordRingElem) = x.parent
deepcopy(x::CobordRingElem) = parent(x)(deepcopy(x.f))

Base.show(io::IO, R::CobordRing) = print(io, "Cobordism Ring")

(R::CobordRing)(f::ChRingElem) = begin
  parent(f) == R.R && return CobordRingElem(R, R.n, f)
  n = length(gens(parent(f)))
  R[n]
  CobordRingElem(R, R.n, f.f(gens(R.R)[1:n]...))
end
(R::CobordRing)(n::T) where T <: Union{Int, Rational, fmpz, fmpq} = (R[1]; CobordRingElem(R, R.n, R.R(n)))
(R::CobordRing)() = R(0)
zero(R::CobordRing) = R(0)
one(R::CobordRing) = R(1)
(R::CobordRing)(x::CobordRingElem) = (@assert parent(x) == R; x)
# get the n-th generator, extending the ring if necessary
function Base.getindex(R::CobordRing, n::Int)
  if R.n < n
    R.n = max(2R.n, 1) # double the number of generators
    S = Nemo.PolynomialRing(QQ, ["[P$i]" for i in 1:R.n])[1]
    R.R = ChRing(S, collect(1:R.n))
  end
  R(gens(R.R)[n])
end
Base.getindex(x::CobordRingElem, n::Int) = x.parent(x.f[n])

mul!(c::CobordRingElem, a::CobordRingElem, b::CobordRingElem) = (ab = a * b; c.n = ab.n; c.f = ab.f; c)
add!(c::CobordRingElem, a::CobordRingElem, b::CobordRingElem) = (ab = a + b; c.n = ab.n; c.f = ab.f; c)
addeq!(a::CobordRingElem, b::CobordRingElem) = (ab = a + b; a.n = ab.n; a.f = ab.f; a)

function (R::CobordRing)(X::Variety)
  if X isa AbsVariety
    @assert integral(X(0)) isa fmpq
  end
  R(chern_numbers(X))
end

@doc Markdown.doc"""
    cobordism_class(X::Variety)
Construct the cobordism class of a variety $X$."""
cobordism_class(X::Variety) = Omega(X)

function (R::CobordRing)(c::Dict{T, fmpq}) where T <: Partition
  P = collect(keys(c))
  n = sum(P[1])
  @assert all(x -> sum(x) == n, P)
  R[n]
  p = gens(R.R)[1:n]
  v = _to_Pn(n, c)
  R(sum(v[i] * prod(p[d] for d in λ) for (i, λ) in enumerate(partitions(n))))
end

function expressify(x::CobordRingElem; context = nothing)
  expressify(x.f, context = context)
end

for T in [:Int, :Rational, :fmpz, :fmpq, :n_Q]
  @eval promote_rule(::Type{CobordRingElem}, ::Type{$T}) = CobordRingElem
end

-(x::CobordRingElem) = x.parent(-x.f)
+(x::CobordRingElem, y::CobordRingElem) = (@assert parent(x) == parent(y); R = parent(x); R(R(x.f).f + R(y.f).f))
-(x::CobordRingElem, y::CobordRingElem) = (@assert parent(x) == parent(y); R = parent(x); R(R(x.f).f - R(y.f).f))
*(x::CobordRingElem, y::CobordRingElem) = (@assert parent(x) == parent(y); R = parent(x); R(R(x.f).f * R(y.f).f))
==(x::CobordRingElem, y::CobordRingElem) = (@assert parent(x) == parent(y); R = parent(x); R(x.f).f == R(y.f).f)
^(x::CobordRingElem, n::Int) = x.parent(x.f^n)

function dim(x::CobordRingElem)
  n = total_degree(x.f)
  x == x[n] || error("the element is not equidimensional")
  n
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
  Pd = partitions(d)
  f = λ -> (ans = repeat([0], x.n); for i in λ if i <= x.n ans[i] += 1 end end; ans)
  c = _chern_Pn(d)[[i for (i, λ) in enumerate(Pd) if λ in P], :] * Nemo.matrix(QQ, [coeff(x.f, f(λ)) for λ in Pd][:, :])
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
