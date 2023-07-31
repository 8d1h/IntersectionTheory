function collect(W::WeylGroup)
  W.(GG.Elements(W.X))
end
function Base.getindex(W::WeylGroup, i::Int)
  W(W.gens[i])
end
function gens(W::WeylGroup)
  W.(W.gens)
end

function ^(x::ChRingElem, w::WeylGroupElem)
  W = w.parent
  @assert weyl_group(get_attribute(parent(x), :variety)) == W
  get_attribute(W, :action)(w, x.f)
end

# XXX the GAP code in Sage is faster
# https://github.com/sagemath/sage/blob/master/src/sage/combinat/root_system/reflection_group_element.pyx
function length(w::WeylGroupElem)
  W = w.parent
  GG.IsPermGroup(W.X) && return GG.Length(GG.PreImagesRepresentative(W.p, w.X))
  GG.Length(GG.Factorization(W.X, w.X))
end

function _factor(w::WeylGroupElem)
  GAP.gap_to_julia(GG.ExtRepOfObj(GG.PreImagesRepresentative(w.parent.p, w.X)))[1:2:end]
end

function basis(W::WeylGroup)
  if get_attribute(W, :basis) === nothing
    ans = Dict{Int, Vector{WeylGroupElem}}()
    for w in collect(W)
      l = length(w)
      if !(l in keys(ans))
	ans[l] = [w]
      else
	push!(ans[l], w)
      end
    end
    l_max = max(collect(keys(ans))...)
    set_attribute!(W, :basis => [ans[i] for i in 0:l_max])
  end
  get_attribute(W, :basis)
end

function betti(W::WeylGroup)
  length.(basis(W))
end

function longest_element(W::WeylGroup)
  basis(W)[end][1]
end

function weyl_group(F::AbsVariety)
  get_attribute(F, :weyl_group)
end

# This uses the description in [Bernstein, Gel'fand, Gel'fand - Schubert cells and cohomology of the spaces G/P].
# Probably there are more efficient ways
# TODO other Lie types, as well as other parabolic subgroups in general
@doc Markdown.doc"""
    schubert_class(F::AbsVariety, w::WeylGroupElem)

Return the Schubert class $\sigma_w$ on a complete flag variety $F$.
"""
function schubert_class(F::AbsVariety, w::WeylGroupElem)
  @assert weyl_group(F) == w.parent
  W = weyl_group(F)
  word = _factor(w)
  l = length(word)
  roots = get_attribute(F, :roots)
  ans = F(0)
  for (x, y) in zip(basis(l, F), dual_basis(l, F))
    Ax = x
    for i in word
      Ax = F((Ax.f - Ax^W[i]) ÷ roots[i])
    end
    ans += Ax * y
  end
  ans
end

# for working with Betti numbers
function div(u::Vector, v::Vector)
  a = div(u[1], v[1])
  length(u) == length(v) && return [a]
  u = vcat(u[2:length(v)] - a * v[2:end], u[length(v)+1:end])
  pushfirst!(div(u, v), a)
end

function homogeneous_variety(G::String, I=nothing; symbol::String="c", base::Ring=QQ, param::Union{String, Vector{String}}=String[])
  base, param = _parse_base(base, param)
  typ, n = G[1], parse(Int, G[2:end])
  typ == 'A' && return flag(collect(1:n+1)..., base=base, symbol=symbol)
  syms = _parse_symbol(symbol, 1:n)
  ord = prod(ordering_dp(1) for i in 1:n)
  R, w = polynomial_ring(base, syms, ordering=ord)
  AˣX = ChRing(R, repeat([1], n))
  if typ == 'B'
    rels = [sum(prod(w[i]^2 for i in c) for c in combinations(n, k)) for k in 1:n]
    AˣX.I = std(Ideal(R, rels))
    X = AbsVariety(n^2, AˣX)
    X.bundles = [AbsBundle(X, 1, w[i]) for i in 1:n]
    X.T = sum(dual(X.bundles[i]) * ((2n+1) * OO(X) - sum(X.bundles[j] for j in 1:i)) for i in 1:n) - symmetric_power(2, dual(sum(X.bundles)))
    X.point = X(prod(1//2 * (-1)^i * w[i]^(2i-1) for i in 1:n))
    set_attribute!(X, :roots => -push!([w[i] - w[i+1] for i in 1:n-1], w[n]))
  elseif typ == 'C'
    rels = [sum(prod(w[i]^2 for i in c) for c in combinations(n, k)) for k in 1:n]
    AˣX.I = std(Ideal(R, rels))
    X = AbsVariety(n^2, AˣX)
    X.bundles = [AbsBundle(X, 1, w[i]) for i in 1:n]
    X.T = sum(dual(X.bundles[i]) * (2n * OO(X) - sum(X.bundles[j] for j in 1:i)) for i in 1:n) - exterior_power(2, dual(sum(X.bundles)))
    X.point = X(prod((-1)^i * w[i]^(2i-1) for i in 1:n))
    set_attribute!(X, :roots => -push!([w[i] - w[i+1] for i in 1:n-1], 2w[n]))
  elseif typ == 'D'
    rels = push!([sum(prod(w[i]^2 for i in c) for c in combinations(n, k)) for k in 1:n], prod(w))
    AˣX.I = std(Ideal(R, rels))
    X = AbsVariety(n^2-n, AˣX)
    X.bundles = [AbsBundle(X, 1, w[i]) for i in 1:n]
    X.T = sum(dual(X.bundles[i]) * (2n * OO(X) - sum(X.bundles[j] for j in 1:i)) for i in 1:n) - symmetric_power(2, dual(sum(X.bundles)))
    X.point = 2X(prod(1//2 * (-w[i]^2)^(i-1) for i in 1:n))
    set_attribute!(X, :roots => -push!([w[i] - w[i+1] for i in 1:n-1], w[n-1] + w[n]))
  end
  set_attribute!(X, :weyl_group => weyl_group(G))
  return param == [] ? X : (X, param)
end
