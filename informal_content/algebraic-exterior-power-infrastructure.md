# Algebraic exterior power infrastructure

For every field L, L-vector space V and degree k, the exterior power Λ^k_L V represents alternating k-linear maps. It is spanned by pure wedges; a basis of V induces the increasing-subset wedge basis. Linear maps act functorially on exterior powers, and an injection of vector spaces induces an injection of exterior powers.

## Mathlib declarations

`exteriorPower.ιMulti`, `exteriorPower.ιMulti_span`, `exteriorPower.alternatingMapLinearEquiv`, `exteriorPower.map` in `Mathlib/LinearAlgebra/ExteriorPower/Basic.lean`; `Module.Basis.exteriorPower` in `Mathlib/LinearAlgebra/ExteriorPower/Basis.lean`. The injectivity specialization follows from splitting a vector-space injection and functoriality.
