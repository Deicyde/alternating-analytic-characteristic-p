import AlternatingAnalytic.Analysis.LaurentSubfield
import Mathlib.Algebra.Field.ULift

/-! A Laurent coefficient field in the universe of the prescribed base field. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped NNReal

namespace AlternatingAnalytic

universe u

/-- Lifting the finite prime field puts the Laurent construction in the same
universe as the prescribed complete field, without changing its mathematics. -/
theorem exists_sameUniverse_laurentField_normedAlgebra
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K]
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    ∃ (r : ℝ≥0) (hr0 : 0 < r) (hr1 : r < 1),
      letI : Fact (0 < r) := ⟨hr0⟩
      letI : Fact (r < 1) := ⟨hr1⟩
      Nonempty (NormedAlgebra (LaurentField (ULift.{u} (ZMod p)) r) K) := by
  let : IsUltrametricDist K := charP_isUltrametricDist p
  obtain ⟨t, ht0, ht1⟩ := NormedField.exists_nnnorm_lt_one K
  refine ⟨‖t‖₊, ht0, ht1, ?_⟩
  let : Fact (0 < ‖t‖₊) := ⟨ht0⟩
  let : Fact (‖t‖₊ < 1) := ⟨ht1⟩
  let f : ULift.{u} (ZMod p) →+* K :=
    (ZMod.castHom (dvd_refl p) K).comp ULift.ringEquiv.toRingHom
  obtain ⟨g, hg, -⟩ := exists_isometric_laurentField_embedding
    (ULift.{u} (ZMod p)) ‖t‖₊ f t rfl
  exact ⟨laurentFieldNormedAlgebra (ULift.{u} (ZMod p)) ‖t‖₊ g hg⟩

end AlternatingAnalytic
