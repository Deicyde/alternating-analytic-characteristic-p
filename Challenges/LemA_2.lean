import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.Algebra.CharP.Defs

/-!
# Lemma A.2 (positive characteristic is nonarchimedean), p. 25

Paper statement: "A normed field of characteristic p > 0 is nonarchimedean."

## Formalization notes
* "Characteristic p > 0" is `CharP K p` with `0 < p`; primality of `p` is derived.
* "Nonarchimedean" is Mathlib's `IsUltrametricDist K`, equivalent to `‖x + y‖ ≤ max ‖x‖ ‖y‖`.
-/

namespace AlternatingAnalyticChallenge.LemA_2

/-- A normed field of positive characteristic is nonarchimedean. -/
theorem nonarchimedean_of_charP_pos
    (K : Type*) [NormedField K] (p : ℕ) [CharP K p] (hp : 0 < p) :
    IsUltrametricDist K := by
  sorry

end AlternatingAnalyticChallenge.LemA_2
