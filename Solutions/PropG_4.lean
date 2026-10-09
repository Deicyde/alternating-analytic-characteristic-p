import Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSeminorm
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Group.Ultra
import AlternatingAnalytic.Tensor.L1Projection.Optimal

/-!
# Proof of Proposition G.4

Uses `AlternatingAnalytic.L1Projection.sInf_norm_projection_eq_factorial` and
`AlternatingAnalytic.L1Projection.not_universalAnalyticReflection` from
`AlternatingAnalytic/Tensor/L1Projection/Optimal.lean`.
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
      (n.factorial : ℝ) :=
  AlternatingAnalytic.L1Projection.sInf_norm_projection_eq_factorial (K := K) (I := I) n

/-- Proposition G.4, second part: `ℓ¹(I,K)` does not have universal analytic reflection. -/
theorem l1_not_universalAnalyticReflection_part2
    (K : Type uK) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (I : Type uI) [Infinite I] :
    ¬ UniversalAnalyticReflection K (lp (fun _ : I => K) 1) :=
  AlternatingAnalytic.L1Projection.not_universalAnalyticReflection (K := K) (I := I)

end AlternatingAnalyticChallenge.PropG_4
