import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.Algebra.CharP.Defs

/-!
# Lemma A.2 (positive characteristic is nonarchimedean), p. 24

Paper statement: "A normed field of characteristic p > 0 is nonarchimedean."

Formalization notes:
* "Characteristic p > 0" is `CharP K p` together with `0 < p`; primality of `p` is not
  assumed (it follows, since a field has prime or zero characteristic).
* "Nonarchimedean" is Mathlib's `IsUltrametricDist K`, i.e.
  `dist x z ≤ max (dist x y) (dist y z)`; for a normed field this is equivalent to
  `‖x + y‖ ≤ max ‖x‖ ‖y‖`.
* No completeness or nontriviality of the norm is assumed, as in the paper.
* No definitions are introduced.
-/

namespace AlternatingAnalyticChallenge.LemA_2

/-- **Lemma A.2.** A normed field of positive characteristic is nonarchimedean. -/
theorem nonarchimedean_of_charP_pos
    (K : Type*) [NormedField K] (p : ℕ) [CharP K p] (hp : 0 < p) :
    IsUltrametricDist K := by
  sorry

end AlternatingAnalyticChallenge.LemA_2
