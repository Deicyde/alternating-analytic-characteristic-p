import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Fintype.Perm

/-! Ordinary triangle-inequality determinant bounds for finite-coordinate lifts. -/

namespace AlternatingAnalytic

/-- The Leibniz determinant estimate with a separate nonnegative weight for each
row and column. The factorial is a real counting constant, with no restriction
on the characteristic of the field. -/
theorem norm_det_le_factorial_mul_prod {K : Type*} [NormedField K] {k : ℕ}
    (a : Matrix (Fin k) (Fin k) K) (r c : Fin k → ℝ)
    (_hr : ∀ i, 0 ≤ r i) (_hc : ∀ j, 0 ≤ c j)
    (hbound : ∀ i j, ‖a i j‖ ≤ r i * c j) :
    ‖a.det‖ ≤ (k.factorial : ℝ) * (∏ i, r i) * ∏ j, c j := by
  classical
  rw [Matrix.det_apply]
  calc
    _ ≤ ∑ σ : Equiv.Perm (Fin k), ‖Equiv.Perm.sign σ • ∏ j, a (σ j) j‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin k), (∏ i, r i) * ∏ j, c j := by
      apply Finset.sum_le_sum
      intro σ _
      rw [norm_units_zsmul, norm_prod]
      calc
        _ ≤ ∏ j, r (σ j) * c j :=
          Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) (fun j _ => hbound _ _)
        _ = (∏ i, r i) * ∏ j, c j := by
          rw [Finset.prod_mul_distrib, Equiv.prod_comp σ]
    _ = _ := by simp [Fintype.card_perm, mul_assoc]

end AlternatingAnalytic
