import Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSeminorm
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Group.Ultra

/-!
# Proposition G.4 (projection norms for ℓ¹), p. 58

Paper statement (Appendix G: `T_n(P)`, `Δ_n(P)` and projections onto `Δ_n(P)` are as in
Proposition G.1; `ℓ¹(I,K)` carries the sum norm; universal analytic reflection is
Definition G.2):
"If K is nonarchimedean and complete, and I is infinite, then
inf{‖R‖ : R : T_n(ℓ¹(I,K)) → Δ_n(ℓ¹(I,K)) is a bounded projection} = n!.
Consequently ℓ¹(I,K) does not have universal analytic reflection."

## Formalization notes

* `ℓ¹(I,K)` is Mathlib's `lp (fun _ : I => K) 1`. The degree satisfies `1 ≤ n`.
* `part1`: the infimum is a real `sInf`. Since `sInf ∅ = 0`, the equation also says a
  projection exists.
* `part2`: Definition G.2 is encoded as in Theorem G.3, with test targets in
  `Type (max uK uI)`. Restricting the test targets weakens Definition G.2, so the negation is
  stronger than the paper's statement.
* `TensorPower`, `diagonalTensor`, `DiagonalSpan` and `UniversalAnalyticReflection` are the
  definitions of the Proposition G.1 and Theorem G.3 challenges.
-/

namespace AlternatingAnalyticChallenge.PropG_4

universe uK uP uI

open scoped TensorProduct

/-- The completed projective tensor power `T_n(P)`: the Hausdorff completion of
`⨂[K] (i : Fin n), P` with Mathlib's projective seminorm. -/
abbrev TensorPower (K : Type uK) (P : Type uP) [NontriviallyNormedField K]
    [NormedAddCommGroup P] [NormedSpace K P] (n : ℕ) :=
  UniformSpace.Completion (⨂[K] _ : Fin n, P)

/-- The pure power `x^{⊗ n}` in `T_n(P)`. -/
noncomputable def diagonalTensor (K : Type uK) {P : Type uP} [NontriviallyNormedField K]
    [NormedAddCommGroup P] [NormedSpace K P] (n : ℕ) (x : P) : TensorPower K P n :=
  ((⨂ₜ[K] _ : Fin n, x : ⨂[K] _ : Fin n, P) : UniformSpace.Completion (⨂[K] _ : Fin n, P))

/-- `Δ_n(P)`: the closed linear span of the pure powers `x^{⊗ n}` in `T_n(P)`. -/
noncomputable def DiagonalSpan (K : Type uK) (P : Type uP) [NontriviallyNormedField K]
    [NormedAddCommGroup P] [NormedSpace K P] (n : ℕ) : Submodule K (TensorPower K P n) :=
  (Submodule.span K (Set.range (diagonalTensor K (P := P) n))).topologicalClosure

/-- Definition G.2, universal analytic reflection, as in Theorem G.3: maps on an open `U`
are total maps and test targets are in `Type (max uK uP)`. -/
def UniversalAnalyticReflection (K : Type uK) (P : Type uP) [NontriviallyNormedField K]
    [NormedAddCommGroup P] [NormedSpace K P] : Prop :=
  ∀ (Z : Type (max uK uP)) [NormedAddCommGroup Z] [NormedSpace K Z] [CompleteSpace Z],
    ∀ (W : Submodule K Z), IsClosed (W : Set Z) →
    ∀ (U : Set P), IsOpen U → ∀ f : P → W,
      AnalyticOnNhd K (fun x => (f x : Z)) U → AnalyticOnNhd K f U

/-- Proposition G.4, first part: the infimum of the norms of projections
`T_n(ℓ¹(I,K)) → Δ_n(ℓ¹(I,K))` is `n!`. -/
theorem l1_inf_norm_tensor_projection_eq_factorial_part1
    (K : Type uK) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (I : Type uI) [Infinite I] (n : ℕ) (hn : 1 ≤ n) :
    sInf {c : ℝ | ∃ R : TensorPower K (lp (fun _ : I => K) 1) n →L[K]
        DiagonalSpan K (lp (fun _ : I => K) 1) n,
        (∀ t : DiagonalSpan K (lp (fun _ : I => K) 1) n,
          R (t : TensorPower K (lp (fun _ : I => K) 1) n) = t) ∧ ‖R‖ = c} =
      (n.factorial : ℝ) := by
  sorry

/-- Proposition G.4, second part: `ℓ¹(I,K)` does not have universal analytic reflection. -/
theorem l1_not_universalAnalyticReflection_part2
    (K : Type uK) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (I : Type uI) [Infinite I] :
    ¬ UniversalAnalyticReflection K (lp (fun _ : I => K) 1) := by
  sorry

end AlternatingAnalyticChallenge.PropG_4
