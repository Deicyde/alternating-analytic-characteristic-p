import AlternatingAnalytic.Analysis.LaurentSubfield
import Mathlib.Algebra.Field.ULift

/-!
# A Laurent subfield of a complete field of characteristic p

Every complete nontrivially normed field `K` of characteristic `p` is a normed algebra over some
`F_p((X))` with `0 < |X| < 1`, as in step (1) of the proof of Theorem 6.1(1). The prime field is
lifted to the universe of `K`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped NNReal

namespace AlternatingAnalytic

universe u

/-- `K` is a normed algebra over `F_p((X))` for some radius `0 < r < 1`, with `F_p` lifted to the
universe of `K`. -/
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
