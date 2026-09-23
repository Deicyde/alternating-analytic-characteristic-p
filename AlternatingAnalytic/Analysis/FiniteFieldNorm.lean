import AlternatingAnalytic.Analysis.PositiveCharacteristic

/-! Finite coefficient fields have trivial norm in every normed field extension. -/

namespace AlternatingAnalytic

variable {κ K : Type*} [Field κ] [Finite κ] [NormedField K]

/-- A nonzero element of a finite field has norm one in any normed field image. -/
theorem norm_finiteField_map (f : κ →+* K) (c : κ) (hc : c ≠ 0) : ‖f c‖ = 1 := by
  classical
  let : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ - 1 ≠ 0 := by
    have := Fintype.one_lt_card (α := κ)
    omega
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) hcard).mp
  rw [← norm_pow, ← map_pow, FiniteField.pow_card_sub_one_eq_one c hc, map_one, norm_one]

theorem norm_finiteField_map_le_one (f : κ →+* K) (c : κ) : ‖f c‖ ≤ 1 := by
  by_cases hc : c = 0
  · simp [hc]
  · exact (norm_finiteField_map f c hc).le

end AlternatingAnalytic
