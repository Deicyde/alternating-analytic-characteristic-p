# Constant coefficient of a single Laurent wedge

For x₁,…,x_k∈E₁ there is η_x∈Λ^k_κE₀ whose determinant array is coeff₀(Ω^{K₁}(x₁∧⋯∧x_k)), and sdim(η_x)≤kM_r∏_b‖x_b‖. If all factors are nonzero, put ν_b=ν(x_b), l=-∑ν_b and N={n∈Z^k:n_b≥ν_b,∑n_b=0}. Then η_x=∑_{n∈N}x_{1,[n₁]}∧⋯∧x_{k,[n_k]}; N is empty if l<0 and finite otherwise.

Complete local actual constant-coefficient determinant witness, explicit finite Laurent expansion and support dimension at most k(l+1), hence at most k*M_r times the product of input norms. Truncation stability is proved for genuine bounded arrays. laurent-wedge-coefficient-independent verifies 29 owned declarations; laurent-embedding-stability-independent separately verifies the stability helper. These are local implementations, not upstream Mathlib membership claims. Actual builds and exhaustive owned-declaration axiom probes returned zero; only standard axioms, unchanged sources. Statement jury pending.
