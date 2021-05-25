function collect(W::WeylGroup)
  W.(GG.Elements(W.X))
end
function Base.getindex(W::WeylGroup, i::Int)
  W(W.gens[i])
end
function gens(W::WeylGroup)
  W.(W.gens)
end

(w::WeylGroupElem)(n::Int) = GG.OnPoints(n, w.X)

function (Vector)(w::WeylGroupElem)
  W = w.parent
  W.typ == 'A' && return w.(1:length(W.gens)+1)
  error("not implemented")
end

function ^(x::ChRingElem, w::WeylGroupElem)
  @assert weyl_group(get_special(parent(x), :variety)) == w.parent
  x.parent(Singular.permute_variables(x.f, Vector(w), x.parent.R))
end

# XXX the GAP code in Sage is faster
# https://github.com/sagemath/sage/blob/master/src/sage/combinat/root_system/reflection_group_element.pyx
function length(w::WeylGroupElem)
  GG.Length(GG.PreImagesRepresentative(w.parent.p, w.X))
end

function _factor(w::WeylGroupElem)
  GAP.gap_to_julia(GG.ExtRepOfObj(GG.PreImagesRepresentative(w.parent.p, w.X)))[1:2:end]
end

function basis(W::WeylGroup)
  if get_special(W, :basis) === nothing
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
    set_special(W, :basis => [ans[i] for i in 0:l_max])
  end
  get_special(W, :basis)
end

function betti(W::WeylGroup)
  length.(basis(W))
end

function longest_element(W::WeylGroup)
  basis(W)[end][1]
end

function weyl_group(F::AbsVariety)
  get_special(F, :weyl_group)
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
  c = gens(F)
  # works for type A only
  # Note the sign: `c` are first Chern classes of the tautological bundles,
  # the Schubert polynomials should use the negative of these
  roots = [-(c[i] - c[i+1]) for i in 1:length(c)-1]
  ans = F(0)
  for (x, y) in zip(basis(l, F), dual_basis(l, F))
    Ax = x
    for i in word
      Ax = F((Ax - Ax^W[i]).f ÷ roots[i].f)
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
