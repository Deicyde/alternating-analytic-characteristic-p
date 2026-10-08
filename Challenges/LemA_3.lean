import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Lemma A.3 (finite-dimensional spaces over complete fields), pp. 24-25

Paper statement: "Let K be a complete nontrivially normed field and U a finite-dimensional
normed K-space. Then every linear functional on U is bounded, and U is complete."

Formalization notes:
* "Linear functional" is an algebraic linear map `U →ₗ[K] K`; "bounded" is the existence of
  `C` with `‖g x‖ ≤ C * ‖x‖` for all `x`.
* The two assertions are stated as two theorems (`part1`, `part2`).
* No definitions are introduced.
-/

namespace AlternatingAnalyticChallenge.LemA_3

/-- **Lemma A.3, part 1.** Every linear functional on `U` is bounded. -/
theorem part1_linearFunctional_bounded
    (K : Type*) [NontriviallyNormedField K] [CompleteSpace K]
    (U : Type*) [NormedAddCommGroup U] [NormedSpace K U] [FiniteDimensional K U] :
    ∀ g : U →ₗ[K] K, ∃ C : ℝ, ∀ x : U, ‖g x‖ ≤ C * ‖x‖ := by
  sorry

/-- **Lemma A.3, part 2.** `U` is complete. -/
theorem part2_completeSpace
    (K : Type*) [NontriviallyNormedField K] [CompleteSpace K]
    (U : Type*) [NormedAddCommGroup U] [NormedSpace K U] [FiniteDimensional K U] :
    CompleteSpace U := by
  sorry

end AlternatingAnalyticChallenge.LemA_3
