# Algebraic tensor products and scalar extension

For a field L and L-vector spaces V,W, V⊗_L W represents bilinear maps. Every tensor is a finite sum of elementary tensors. Linear maps act on tensor factors. When W=K' is a field extension, scalar multiplication on the second tensor factor makes V⊗_L K' into a K'-vector space, with (cv)⊗λ=v⊗cλ for c∈L.

## Mathlib declarations

`TensorProduct.lift`, `TensorProduct.lift.tmul`, `TensorProduct.map` and the standard tensor-product module structures in `Mathlib/LinearAlgebra/TensorProduct/Basic.lean`. The construction carries no projective norm until the analytic scalar-extension node.
