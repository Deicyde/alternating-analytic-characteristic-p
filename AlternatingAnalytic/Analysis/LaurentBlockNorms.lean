import AlternatingAnalytic.Analysis.LaurentCompletedCoefficient

/-! Exact norms and quantitative growth of the actual Laurent block wedges. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NNReal BoundedContinuousFunction

namespace AlternatingAnalytic

variable (κ : Type*) [Field κ] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] (k : ℕ)

/-- Evaluating a coordinate block on its own indices gives the identity determinant. -/
theorem completedExteriorArray_laurentBlockWedge (j : ℕ) :
    completedExteriorArray (LaurentField κ r) ℕ k (laurentBlockWedge κ r k j)
      (fun i : Fin k => k * j + i.val + 1) = 1 := by
  classical
  rw [laurentBlockWedge, completedExteriorArray_wedge]
  have hm : (fun i l : Fin k =>
      constantLaurentArray κ r (Pi.single (k * j + l.val + 1) (1 : κ))
        (k * j + i.val + 1)) = (1 : Matrix (Fin k) (Fin k) (LaurentField κ r)) := by
    ext i l
    by_cases h : i = l
    · subst l
      simp [constantLaurentArray_apply]
    · have hval : i.val ≠ l.val := fun he => h (Fin.ext he)
      simp [constantLaurentArray_apply, h, hval]
  rw [hm, Matrix.det_one]

/-- Every actual consecutive block wedge has norm exactly one. -/
theorem norm_laurentBlockWedge (j : ℕ) : ‖laurentBlockWedge κ r k j‖ = 1 := by
  apply le_antisymm (norm_laurentBlockWedge_le_one κ r k j)
  have h := (completedExteriorArray (LaurentField κ r) ℕ k
    (laurentBlockWedge κ r k j)).norm_coe_le_norm (fun i : Fin k => k * j + i.val + 1)
  rw [completedExteriorArray_laurentBlockWedge, norm_one] at h
  exact h.trans (norm_completedExteriorArray_le _ _ _ _)

/-- The ordinary triangle inequality gives the matching linear upper bound. -/
theorem norm_sum_laurentBlockWedge_le (N : ℕ) :
    ‖∑ j ∈ Finset.range N, laurentBlockWedge κ r k j‖ ≤ (N : ℝ) := by
  calc
    _ ≤ ∑ j ∈ Finset.range N, ‖laurentBlockWedge κ r k j‖ := norm_sum_le _ _
    _ = N := by simp [norm_laurentBlockWedge]

/-- The coefficient support estimate gives the lower block-sum bound for every radius. -/
theorem le_norm_sum_laurentBlockWedge (hk : 2 ≤ k) (N : ℕ) :
    (N : ℝ) / geometricWeightMaximum r ≤
      ‖∑ j ∈ Finset.range N, laurentBlockWedge κ r k j‖ := by
  let α : Fin k := ⟨0, by omega⟩
  exact exteriorCoefficient_block_growth hk (completedLaurentCoefficient κ r ℕ k α)
    (laurentBlockWedge κ r k)
    (fun j => completedLaurentCoefficient_constant_wedge κ r ℕ k α
      (fun i => Pi.single (k * j + i.val + 1) (1 : κ)))
    (zero_lt_one.trans_le (one_le_geometricWeightMaximum r))
    (completedLaurentCoefficient_support_le κ r ℕ k α) N

omit [Fact (0 < r)] in
/-- For radii at most one half the geometric support constant is exactly one. -/
theorem geometricWeightMaximum_eq_one (hr : (r : ℝ) ≤ 1 / 2) :
    geometricWeightMaximum r = 1 := by
  apply le_antisymm _ (one_le_geometricWeightMaximum r)
  unfold geometricWeightMaximum
  exact geometricWeight_le_one r.coe_nonneg hr _

/-- At small radii the norm of an N-block sum is exactly N. -/
theorem norm_sum_laurentBlockWedge_eq (hk : 2 ≤ k) (hr : (r : ℝ) ≤ 1 / 2) (N : ℕ) :
    ‖∑ j ∈ Finset.range N, laurentBlockWedge κ r k j‖ = (N : ℝ) := by
  apply le_antisymm (norm_sum_laurentBlockWedge_le κ r k N)
  simpa only [geometricWeightMaximum_eq_one r hr, div_one] using
    le_norm_sum_laurentBlockWedge κ r k hk N

end AlternatingAnalytic
