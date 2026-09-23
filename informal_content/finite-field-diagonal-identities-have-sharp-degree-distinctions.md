# Finite-field diagonal identities have sharp degree distinctions

For a degree-k lift over a finite field F_q, Pw implies Pol when k≤q. For k≥q+1 this implication fails in general. If k!=0, Pol1 need not imply Pw. These are optional sharpness statements for the distinction between pointwise and formal polynomial identities.

## Proof

A homogeneous scalar polynomial of degree e≤q vanishing on F_q^m is zero: reduced monomials with each exponent≤q-1 form a basis of functions on F_q^m, as seen by point-indicator polynomials. A non-reduced degree-e monomial can only be λ_i^q when e=q; reducing it to λ_i preserves distinctness among the original homogeneous monomials. Thus vanishing gives zero coefficients. Apply coordinate functionals to the finite-dimensional coefficient span for the vector-valued statement. For k≥q+1 take D=0 and Ψ(a;x)=θ(a)(x₁∧⋯∧x_k), where θ(a₁,…,a_k)=[g₁(a₁)⋯g₁(a_q)g₂(a_{q+1})-g₁(a₁)g₂(a₂)⋯g₂(a_{q+1})]∏_{i=q+2}^k g₃(a_i), with suitable dual-coordinate vectors. Its diagonal vanishes because c^q=c, but its polarized coefficient of multiplicity (q,1,k-q-1) is a nonzero wedge. Finally θ'(a)=∏g₁(a_i) gives Pol1 when k!=0 because its permutation sum is k! times one product, while its diagonal at g₁(a)=1 is nonzero.
