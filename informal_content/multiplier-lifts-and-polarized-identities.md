# Multiplier lifts and polarized identities

For a field L, vector spaces A,V and a linear family D:A→End_L(V), a degree-k lift is a map Ψ:A^k×V^k→Λ^kV multilinear in all 2k slots and alternating in the V slots. Pw is Ψ(a,…,a;x)=D_a x₁∧⋯∧D_a x_k. Pol equates the coefficient sums over functions f:[k]→[m] of each fixed multiplicity type α in the expansion at ∑λ_i b_i. Pol1 is ∑_{σ∈S_k}Ψ(b_σ;x)=∑_{σ∈S_k}D_{b_{σ(1)}}x₁∧⋯∧D_{b_{σ(k)}}x_k. Over every field Pol⇒Pw⇒Pol1; over an infinite field Pw⇒Pol.

## Proof

Pol⇒Pw is the one-variable coefficient identity. For Pw⇒Pol1 take the alternating sum over subsets S⊆[k] of Pw at b_S=∑_{i∈S}b_i, with coefficient (-1)^(k-|S|). Multilinearity assigns a map f:[k]→[k] the coefficient ∑_{S⊇range f}(-1)^(k-|S|), equal to 1 exactly when f is surjective and 0 otherwise. Surjections of [k] to itself are permutations. For the infinite-field implication expand both sides of Pw at ∑λ_i b_i as a vector-valued polynomial and use coefficient uniqueness. No division by k! occurs.
