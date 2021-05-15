```@meta
CurrentModule = IntersectionTheory
DocTestSetup = quote
  using IntersectionTheory
end
```
```@setup repl
using IntersectionTheory
```
# Morphisms
## Operators
```@docs
pullback
pushforward
*(f::AbsVarietyHom, g::AbsVarietyHom)
dim(f::AbsVarietyHom)
tangent_bundle(f::AbsVarietyHom)
cotangent_bundle(f::AbsVarietyHom)
todd(f::AbsVarietyHom)
```
## Blowup
```@docs
blowup
```
### Examples
```@repl repl
P = proj(2)
Bl, E = blowup(point() → P)
euler(Bl)
integral(pushforward(E → Bl, E(1))^2)
```
