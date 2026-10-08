import AlternatingAnalytic.Algebra.DeterminantArray
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.Perm.Sign

/-!
# Remark B.15 (when k! is invertible: the normalized lift), p. 34

Setting (Appendix B.3-B.5): `L` is a finite field, `V = L^ℕ`, `ux` is the coordinatewise
product; `sdim` is the support dimension (Definition B.1); `Ω` is the determinant array; for a
cluster `C` (four points `C(1) < ⋯ < C(4)`), `s_C = ∑ᵢ sᵢ e_{C(i)}` and `w_C = ∑ᵢ wᵢ e_{C(i)}` with
`s = (1, 0, -1, 0)`, `w = (1, -1, 1, -1)`; the cluster value of a lift `Ψ` is
`χ(C₁, …, C_k) = Ω_{Ψ(s_{C₁}, …; w_{C₁}, …)}(C₁(1), …, C_k(1))`.

Paper statement: "The vanishing of k! is essential. If instead k! ≠ 0 in L, the normalized
alternatization Ψ_alt(u; x) := (1/k!) ∑_{σ ∈ S_k} (u_{σ(1)} x₁) ∧ ⋯ ∧ (u_{σ(k)} x_k) is
alternating in x and satisfies (Pol1). Every summand is supported in the span of the k² vectors
u_i x_j, so sdim(Ψ_alt(u; x)) ≤ k². The preceding homogeneity, cancellation, staircase and
diagonal arguments apply, but now yield χ ≡ 1/k!: for pairwise disjoint clusters only σ = id
survives in Ψ_alt(s_{C₁}, …, s_{C_k}; w_{C₁}, …, w_{C_k}), and the determinant at
(C₁(1), …, C_k(1)) is that of the identity. The final equation k! · (1/k!) = 1 is then
consistent. So the obstruction is exactly the vanishing of k!, not positive characteristic as
such. For example, at (p, k) = (5, 3) every step is consistent, since 3! = 6 = 1 in F₅ and
χ₀ = 1."

Formalization notes:
* Definitions introduced (identical in challenge and solution): `psiAlt L k u x` is the paper's
  formula for `Ψ_alt(u; x)` on `u, x ∈ V^k`, `V = ℕ → L`, with values in `⋀[L]^k (ℕ → L)`
  (`1/k!` is `(k! : L)⁻¹`, the wedge is `exteriorPower.ιMulti`); `opWeight`, `vecWeight`, `sC`,
  `wC` are `s`, `w`, `s_C`, `w_C` (finitely supported, coerced into `V`); `clusterValueAlt` is the
  cluster value of `Ψ_alt`.
* The claims are split into five theorems: `Ψ_alt` is a `2k`-linear map (implicit in calling it
  a lift; stated as existence of a curried multilinear map agreeing with the formula), alternating
  in `x` (vanishing when two vector arguments coincide), (Pol1) for the multipliers, the bound
  `sdim ≤ k²`, and `χ = 1/k!` on pairwise disjoint clusters.
* `sdim` is the library definition `AlternatingAnalytic.exteriorSupportDim` and `Ω` is
  `AlternatingAnalytic.determinantArray`, imported (via `Algebra/DeterminantArray.lean`) only for
  these definitions; the proofs live in `Algebra/NormalizedMultiplierLift.lean`, not imported.
* Domain: in the setting of Theorem B.9(1) the paper's `Ψ_alt` is defined on
  `V_fin^k × V_fin^k`. Here `Ψ_alt` is defined on `V^k × V^k` (`V = ℕ → L`); restricted to
  `V_fin` it is the paper's map, and every claim ((Pol1), alternation, `sdim ≤ k²`) is stated on
  the larger domain, which implies the paper's version. The paper does not restrict the inputs
  of (Pol1) here.
* Not formalized (commentary, not mathematical claims beyond the five theorems): the sentence
  that "the preceding homogeneity, cancellation, staircase and diagonal arguments apply" (the
  Lean statement records only the resulting value `χ = 1/k!`), the remark that
  `k! · (1/k!) = 1` is consistent, the conclusion that the obstruction is exactly the vanishing
  of `k!`, and the example `(p, k) = (5, 3)`.
* "k! ≠ 0 in L" is `hfact : (k.factorial : L) ≠ 0`, assumed in every part as in the remark
  (alternation and the support bound do not need it). `[Finite L]` is the standing context of
  Appendix B.3; none of the claims uses it.
* "Pairwise disjoint clusters" in the last part: `C j` is strictly increasing in its four points
  and distinct slots have no common point. Clusters need not consist of consecutive elements of
  a homogeneous set `H` (the computation does not use `H`), so this is the paper's claim for
  every `H`.
* Paper labels are 1-based, Lean's are 0-based (`C(1)` is `C 0`).
-/

namespace AlternatingAnalyticChallenge.RemB_15

universe u

open Finset

/-- The normalized alternatization `Ψ_alt(u; x) = (1/k!) ∑_σ (u_{σ(1)} x₁) ∧ ⋯ ∧ (u_{σ(k)} x_k)`. -/
noncomputable def psiAlt (L : Type u) [Field L] (k : ℕ) (u x : Fin k → ℕ → L) :
    ⋀[L]^k (ℕ → L) :=
  (k.factorial : L)⁻¹ • ∑ σ : Equiv.Perm (Fin k),
    exteriorPower.ιMulti L k (fun i => fun n => u (σ i) n * x i n)

section ClusterDefinitions

variable {L : Type u} [Field L] {k : ℕ}

/-- The operator-slot weights `s = (1, 0, -1, 0)`. -/
def opWeight : Fin 4 → L := ![1, 0, -1, 0]

/-- The vector-slot weights `w = (1, -1, 1, -1)`. -/
def vecWeight : Fin 4 → L := ![1, -1, 1, -1]

/-- `s_C := ∑ᵢ sᵢ e_{C(i)}`. -/
noncomputable def sC (C : Fin 4 → ℕ) : ℕ →₀ L :=
  ∑ i, opWeight (L := L) i • Finsupp.single (C i) 1

/-- `w_C := ∑ᵢ wᵢ e_{C(i)}`. -/
noncomputable def wC (C : Fin 4 → ℕ) : ℕ →₀ L :=
  ∑ i, vecWeight (L := L) i • Finsupp.single (C i) 1

/-- The cluster value of `Ψ_alt`:
`χ(C₁, …, C_k) = Ω_{Ψ_alt(s_{C₁}, …, s_{C_k}; w_{C₁}, …, w_{C_k})}(C₁(1), …, C_k(1))`. -/
noncomputable def clusterValueAlt (L : Type u) [Field L] (k : ℕ) (C : Fin k → Fin 4 → ℕ) : L :=
  AlternatingAnalytic.determinantArray
    (psiAlt L k (fun j => ⇑(sC (L := L) (C j))) (fun j => ⇑(wC (L := L) (C j))))
    (fun j => C j 0)

end ClusterDefinitions

/-- **Remark B.15, lift.** `Ψ_alt` is a `2k`-linear map `V^k × V^k → Λ^k V`. -/
theorem psiAlt_multilinear {L : Type u} [Field L] [Finite L] {k : ℕ}
    (hfact : (k.factorial : L) ≠ 0) :
    ∃ Ψ : MultilinearMap L (fun _ : Fin k => ℕ → L)
        (MultilinearMap L (fun _ : Fin k => ℕ → L) (⋀[L]^k (ℕ → L))),
      ∀ u x : Fin k → ℕ → L, Ψ u x = psiAlt L k u x := by
  sorry

/-- **Remark B.15, alternation.** `Ψ_alt(u; x)` is alternating in `x`. -/
theorem psiAlt_alternating {L : Type u} [Field L] [Finite L] {k : ℕ}
    (hfact : (k.factorial : L) ≠ 0) (u x : Fin k → ℕ → L) {i j : Fin k}
    (hx : x i = x j) (hij : i ≠ j) :
    psiAlt L k u x = 0 := by
  sorry

/-- **Remark B.15, (Pol1).** `Ψ_alt` satisfies (Pol1) for the multipliers `D_u x = ux`. -/
theorem psiAlt_pol1 {L : Type u} [Field L] [Finite L] {k : ℕ}
    (hfact : (k.factorial : L) ≠ 0) (u x : Fin k → ℕ → L) :
    ∑ σ : Equiv.Perm (Fin k), psiAlt L k (fun j => u (σ j)) x =
      ∑ σ : Equiv.Perm (Fin k),
        exteriorPower.ιMulti L k (fun j => fun n => u (σ j) n * x j n) := by
  sorry

/-- **Remark B.15, support bound.** `sdim(Ψ_alt(u; x)) ≤ k²`. -/
theorem exteriorSupportDim_psiAlt_le {L : Type u} [Field L] [Finite L] {k : ℕ}
    (hfact : (k.factorial : L) ≠ 0) (u x : Fin k → ℕ → L) :
    AlternatingAnalytic.exteriorSupportDim (psiAlt L k u x) ≤ k ^ 2 := by
  sorry

/-- **Remark B.15, cluster value.** For pairwise disjoint clusters the cluster value of `Ψ_alt` is
`1/k!`. -/
theorem clusterValueAlt_eq_inv_factorial {L : Type u} [Field L] [Finite L] {k : ℕ}
    (hfact : (k.factorial : L) ≠ 0) (C : Fin k → Fin 4 → ℕ) (hC : ∀ j, StrictMono (C j))
    (hdisj : ∀ j l, j ≠ l → ∀ p q, C j p ≠ C l q) :
    clusterValueAlt L k C = (k.factorial : L)⁻¹ := by
  sorry

end AlternatingAnalyticChallenge.RemB_15
