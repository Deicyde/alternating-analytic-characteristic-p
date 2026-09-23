# Mathlib foundations

The algebraic and analytic library foundations comprise continuous alternating precomposition, universal exterior powers and their bases, algebraic tensor products, the complete valued Laurent series field, and the infinite finite-color pigeonhole principle. These statements are existing Mathlib declarations; no Ramsey theorem, projective exterior norm, real Laurent norm at an arbitrary parameter, or scalar-extension positivity theorem is included in this cluster.

## Mathlib declarations

- `ContinuousAlternatingMap.compContinuousLinearMapCLM` in `Mathlib/Topology/Algebra/Module/Alternating/Topology.lean`.
- `exteriorPower.ιMulti`, `exteriorPower.alternatingMapLinearEquiv`, `exteriorPower.map_injective_field` and `Module.Basis.exteriorPower` in `Mathlib/LinearAlgebra/ExteriorPower/Basic.lean` and `Basis.lean`.
- `TensorProduct.lift`, `TensorProduct.lift.tmul` and `TensorProduct.map` in `Mathlib/LinearAlgebra/TensorProduct/Basic.lean`.
- `LaurentSeries.valued`, `LaurentSeries.valuation_single_zpow` and `LaurentSeries.instLaurentSeriesComplete` in `Mathlib/RingTheory/LaurentSeries.lean`.
- `Finite.exists_infinite_fiber` in `Mathlib/Data/Fintype/Pigeonhole.lean`.

Finite sums and permutation signs also belong logically to this foundation cluster, but their fine packet remains temporarily in the preliminaries cluster while its active review finishes. Its reparenting changes only the hierarchy and coarse projection, not its statement or proof packet.
