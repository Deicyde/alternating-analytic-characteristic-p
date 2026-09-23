# Determinant arrays and injectivity

For a subspace V⊆L^S define Ω:Λ^k V→ₗ[L](S^k→L) by Ω(y₁∧⋯∧y_k)(c)=det(y_b(c_a)). This map is injective, and its output is alternating in c. Permuting the output coordinates multiplies the value by the permutation sign.

## Proof

The determinant is multilinear and alternating in its columns, giving Ω by the exterior universal property. Row alternation gives the output rule. For injectivity put a given ω in Λ^kU with U finite dimensional. Restricted coordinate evaluations separate U, hence span U*. Choose d=dim U coordinate evaluations forming a dual basis and the corresponding basis u₁,…,u_d of U. Evaluating Ω at the selected coordinates extracts every coefficient of ω in the increasing wedge basis: the relevant minor is 1 for the matching subset and 0 otherwise. If Ωω=0 all coefficients vanish.
