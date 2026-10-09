import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Fintype.Perm

/-!
# A determinant bound

The Leibniz bound `‖det a‖ ≤ k! ∏ rᵢ ∏ cⱼ` when `‖aᵢⱼ‖ ≤ rᵢ cⱼ`, used for the
finite-coordinate lifts of Proposition 4.1(2).
-/

namespace AlternatingAnalytic

/-- If `‖aᵢⱼ‖ ≤ rᵢ cⱼ`, then `‖det a‖ ≤ k! ∏ rᵢ ∏ cⱼ`. Here `k!` is a real number, so
there is no condition on the characteristic. -/
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
