import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.Algebra.CharP.Defs
import AlternatingAnalytic.Analysis.PositiveCharacteristic

/-!
# Proof of Lemma A.2

Uses `charP_isUltrametricDist` (AlternatingAnalytic/Analysis/PositiveCharacteristic.lean).
-/

namespace AlternatingAnalyticChallenge.LemA_2

/-- A normed field of positive characteristic is nonarchimedean. -/
theorem nonarchimedean_of_charP_pos
    (K : Type*) [NormedField K] (p : ℕ) [CharP K p] (hp : 0 < p) :
    IsUltrametricDist K := by
  have : NeZero p := ⟨hp.ne'⟩
  have : Fact p.Prime := CharP.char_is_prime_of_pos K p
  exact charP_isUltrametricDist p

end AlternatingAnalyticChallenge.LemA_2
