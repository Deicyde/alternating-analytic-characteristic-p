import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
# A weighted determinant bound

Over an ultrametric field, if `‖a i j‖ * w i ≤ v j` then `‖det a‖ * ∏ i, w i ≤ ∏ j, v j`.
This bounds the sorted retraction for an orthogonal basis by one.
-/

namespace AlternatingAnalytic

/-- Over an ultrametric field, `‖a i j‖ * w i ≤ v j` implies
`‖det a‖ * ∏ i, w i ≤ ∏ j, v j`. -/
theorem norm_det_mul_prod_le {K ι : Type*} [NormedField K] [IsUltrametricDist K]
    [Fintype ι] [DecidableEq ι] (a : Matrix ι ι K) (w v : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hbound : ∀ i j, ‖a i j‖ * w i ≤ v j) :
    ‖a.det‖ * ∏ i, w i ≤ ∏ j, v j := by
  classical
  obtain ⟨σ, _, hσ⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
    (Finset.univ_nonempty : (Finset.univ : Finset (Equiv.Perm ι)).Nonempty)
    (fun σ => Equiv.Perm.sign σ • ∏ j, a (σ j) j)
  rw [← Matrix.det_apply, norm_units_zsmul, norm_prod] at hσ
  calc
    _ ≤ (∏ j, ‖a (σ j) j‖) * ∏ i, w i :=
      mul_le_mul_of_nonneg_right hσ (Finset.prod_nonneg fun i _ => hw i)
    _ = ∏ j, ‖a (σ j) j‖ * w (σ j) := by
      rw [Finset.prod_mul_distrib, Equiv.prod_comp σ]
    _ ≤ ∏ j, v j := Finset.prod_le_prod₀
      (fun j _ => mul_nonneg (norm_nonneg _) (hw _)) (fun j _ => hbound _ _)

end AlternatingAnalytic
