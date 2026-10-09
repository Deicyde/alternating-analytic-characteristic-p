/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
import AlternatingAnalytic.Analysis.CompletedProjectiveTensor
import Mathlib.Analysis.Analytic.Basic

/-!
# Tensor powers and diagonal spans in independent universes

The completed projective tensor power `T_n(P)`, the pure powers `x^{⊗ n}`, the closed diagonal
span `Δ_n(P)` and universal analytic reflection (Appendix G), with the scalar field and the
parameter space in independent universes. The library's `AlternatingAnalytic.TensorPower` puts
both in one universe; these are the definitions used in the challenge files for Appendix G.
-/

open scoped TensorProduct

namespace AlternatingAnalytic.L1Projection

universe uK uP

/-- The separated completed ordinary projective tensor power `T_n(P)`. -/
abbrev TensorPower (K : Type uK) (P : Type uP) [NontriviallyNormedField K]
    [NormedAddCommGroup P] [NormedSpace K P] (n : ℕ) :=
  UniformSpace.Completion (⨂[K] _ : Fin n, P)

/-- The pure power `x^{⊗ n}` in `T_n(P)`. -/
noncomputable def diagonalTensor (K : Type uK) {P : Type uP} [NontriviallyNormedField K]
    [NormedAddCommGroup P] [NormedSpace K P] (n : ℕ) (x : P) : TensorPower K P n :=
  ((⨂ₜ[K] _ : Fin n, x : ⨂[K] _ : Fin n, P) : UniformSpace.Completion (⨂[K] _ : Fin n, P))

/-- `Δ_n(P)`: the closed linear span of the pure powers in `T_n(P)`. -/
noncomputable def DiagonalSpan (K : Type uK) (P : Type uP) [NontriviallyNormedField K]
    [NormedAddCommGroup P] [NormedSpace K P] (n : ℕ) : Submodule K (TensorPower K P n) :=
  (Submodule.span K (Set.range (diagonalTensor K (P := P) n))).topologicalClosure

/-- Universal analytic reflection, with test targets in `Type (max uK uP)`. -/
def UniversalAnalyticReflection (K : Type uK) (P : Type uP) [NontriviallyNormedField K]
    [NormedAddCommGroup P] [NormedSpace K P] : Prop :=
  ∀ (Z : Type (max uK uP)) [NormedAddCommGroup Z] [NormedSpace K Z] [CompleteSpace Z],
    ∀ (W : Submodule K Z), IsClosed (W : Set Z) →
    ∀ (U : Set P), IsOpen U → ∀ f : P → W,
      AnalyticOnNhd K (fun x => (f x : Z)) U → AnalyticOnNhd K f U

variable {K : Type uK} {P : Type uP} [NontriviallyNormedField K]
  [NormedAddCommGroup P] [NormedSpace K P]

theorem diagonalTensor_eq (n : ℕ) (x : P) :
    diagonalTensor K n x =
      completedProjectiveTensorTprod (K := K) (fun _ : Fin n => P) (fun _ => x) := rfl

theorem diagonalTensor_mem (n : ℕ) (x : P) :
    diagonalTensor K n x ∈ DiagonalSpan K P n :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨x, rfl⟩)

theorem isClosed_diagonalSpan (n : ℕ) :
    IsClosed (DiagonalSpan K P n : Set (TensorPower K P n)) :=
  Submodule.isClosed_topologicalClosure _

instance (n : ℕ) : CompleteSpace (DiagonalSpan K P n) :=
  (isClosed_diagonalSpan (K := K) (P := P) n).completeSpace_coe

theorem norm_diagonalTensor_le (n : ℕ) (x : P) :
    ‖diagonalTensor K n x‖ ≤ ‖x‖ ^ n := by
  calc
    ‖diagonalTensor K n x‖ ≤
        ‖completedProjectiveTensorTprod (K := K) (fun _ : Fin n => P)‖ * ‖x‖ ^ n := by
      simpa [diagonalTensor_eq] using
        (completedProjectiveTensorTprod (K := K) (fun _ : Fin n => P)).le_opNorm
          (fun _ => x)
    _ ≤ 1 * ‖x‖ ^ n := mul_le_mul_of_nonneg_right
      (norm_completedProjectiveTensorTprod_le _) (pow_nonneg (norm_nonneg x) _)
    _ = ‖x‖ ^ n := one_mul _

/-- Every element of the diagonal span lies in any closed submodule containing the pure
powers. -/
theorem diagonalSpan_le {n : ℕ} (S : Submodule K (TensorPower K P n))
    (hS : IsClosed (S : Set (TensorPower K P n))) (h : ∀ x : P, diagonalTensor K n x ∈ S) :
    DiagonalSpan K P n ≤ S :=
  Submodule.topologicalClosure_minimal _
    (Submodule.span_le.mpr (by rintro _ ⟨x, rfl⟩; exact h x)) hS

/-- A map into the diagonal span that fixes the pure powers fixes the whole span. -/
theorem fixes_of_fixes_diagonalTensor {n : ℕ}
    (R : TensorPower K P n →L[K] DiagonalSpan K P n)
    (hR : ∀ x, (R (diagonalTensor K n x) : TensorPower K P n) = diagonalTensor K n x)
    (t : DiagonalSpan K P n) : R (t : TensorPower K P n) = t := by
  have hgen : Set.EqOn ((DiagonalSpan K P n).subtypeL.comp R)
      (ContinuousLinearMap.id K (TensorPower K P n))
      (Set.range (diagonalTensor K (P := P) n)) := by
    rintro _ ⟨x, rfl⟩
    exact hR x
  exact Subtype.ext (ContinuousLinearMap.eqOn_closure_span hgen t.property)

end AlternatingAnalytic.L1Projection
