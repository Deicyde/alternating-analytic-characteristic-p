import AlternatingAnalytic.Analysis.LaurentCoefficients

/-!
# Norm bounds from vanishing coefficients

If all coefficients of a Laurent series (or of a bounded Laurent array) below degree `m`
vanish, its norm is at most `r ^ m`.
-/

open scoped NNReal BoundedContinuousFunction

namespace AlternatingAnalytic

variable (κ : Type*) [Field κ] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)]

/-- If all coefficients of `x` below degree `m` vanish, then `‖x‖ ≤ r ^ m`. -/
theorem laurentField_norm_le_of_coeff_eq_zero (x : LaurentField κ r) (m : ℤ)
    (h : ∀ n : ℤ, n < m → LaurentField.coeff κ r n x = 0) :
    ‖x‖ ≤ (r : ℝ) ^ m := by
  by_cases hx : x = 0
  · subst x
    have hz : ‖(0 : LaurentField κ r)‖ = 0 := norm_zero
    exact hz.le.trans (zpow_nonneg (NNReal.coe_nonneg r) _)
  rw [LaurentField.norm_of_ne_zero κ r x hx]
  apply (zpow_le_zpow_iff_right_of_lt_one₀ (show 0 < (r : ℝ) from (show 0 < r from Fact.out))
    (show (r : ℝ) < 1 from (show r < 1 from Fact.out))).2
  by_contra hm
  exact hx (HahnSeries.coeff_order_eq_zero.mp (h _ (lt_of_not_ge hm)))

theorem boundedLaurent_norm_le_of_coeff_eq_zero {S : Type*} [TopologicalSpace S]
    (f : S →ᵇ LaurentField κ r) (m : ℤ)
    (h : ∀ n : ℤ, n < m → boundedLaurentCoeff κ r n f = 0) :
    ‖f‖ ≤ (r : ℝ) ^ m := by
  apply (BoundedContinuousFunction.norm_le (zpow_nonneg (NNReal.coe_nonneg r) _)).2
  intro s
  apply laurentField_norm_le_of_coeff_eq_zero κ r (f s) m
  intro n hn
  exact congrFun (h n hn) s

end AlternatingAnalytic
