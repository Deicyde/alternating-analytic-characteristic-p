import AlternatingAnalytic.Analysis.LaurentSubfield
import Mathlib.Algebra.Field.Subfield.Basic

/-! Completeness and spherical completeness of the actual embedded Laurent subfield. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped NNReal

namespace AlternatingAnalytic

variable (κ : Type*) [Field κ] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)]
  {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- The actual image of an isometric Laurent embedding has all the completeness
properties used in the scalar-extension argument. -/
theorem laurentField_range_properties (g : LaurentField κ r →+* K) (hg : Isometry g) :
    IsClosed (g.fieldRange : Set K) ∧ CompleteSpace g.fieldRange ∧
      SphericallyCompleteSpace g.fieldRange ∧ ∃ x : g.fieldRange, 1 < ‖x‖ := by
  let e : LaurentField κ r ≃ᵢ g.fieldRange :=
    { g.rangeRestrictFieldEquiv.toEquiv with
      isometry_toFun := by
        intro x y
        change edist (g x) (g y) = edist x y
        exact hg x y }
  have he (x : LaurentField κ r) : ‖e x‖ = ‖x‖ :=
    e.isometry.norm_map_of_map_zero g.rangeRestrictField.map_zero x
  let : CompleteSpace g.fieldRange := e.symm.completeSpace
  refine ⟨hg.isClosedEmbedding.isClosed_range, inferInstance, ?_, ?_⟩
  · have hr0 : (0 : ℝ) < r := show 0 < r from Fact.out
    have hr1 : (r : ℝ) < 1 := show r < 1 from Fact.out
    apply sphericallyCompleteSpace_of_discreteNorm ((one_lt_inv₀ hr0).mpr hr1)
    intro y hy
    obtain ⟨x, rfl⟩ := e.surjective y
    have hx : x ≠ 0 := by
      intro h
      apply hy
      change g.rangeRestrictField x = 0
      rw [h, map_zero]
    refine ⟨-(show LaurentSeries κ from x).order, ?_⟩
    rw [he, LaurentField.norm_of_ne_zero κ r x hx]
    simp [zpow_neg]
  · obtain ⟨x, hx⟩ := NormedField.exists_one_lt_norm (LaurentField κ r)
    exact ⟨e x, (he x).symm ▸ hx⟩

end AlternatingAnalytic
