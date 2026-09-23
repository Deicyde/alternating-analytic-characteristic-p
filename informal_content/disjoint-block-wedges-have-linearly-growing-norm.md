# Disjoint block wedges have linearly growing norm

For every field κ, degree k≥2 and 0<r<1, let ω_j=e_{kj+1}∧⋯∧e_{kj+k} in B, the projective exterior completion over κ((X)). Then ‖ω_j‖=1 and N/M_r≤‖∑_{j<N}ω_j‖≤N for every N≥1. If r≤1/2 the latter norm is exactly N.

## Proof

Each ω_j is a wedge of unit vectors, so has norm≤1; its determinant array takes value 1 at its block, so norm≥1. The triangle inequality gives the upper bound for their sum ω. Its array has entries in κ, hence η(ω)=ω in Λ^k_κE₀. For each coordinate i in a block j<N contract against the k-1 coordinate functionals of the other positions in that block. Contractions of other blocks vanish because all these functionals vanish there and k≥2. In block j, the term of e_i has a permutation minor of determinant ±1; every other term has a zero column. Thus c_φ(ω)=±e_i. The contraction span contains all kN distinct coordinate vectors, so sdim(ηω)≥kN. The support estimate gives kN≤kM_r‖ω‖, yielding the lower bound. M_r=1 gives equality when r≤1/2.
