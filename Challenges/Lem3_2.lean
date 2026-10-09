import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# Lemma 3.2 (smooth descent), p. 8

Standing assumptions of Section 3: "`K` is nontrivially normed, `P, W, Z` are normed `K`-spaces,
and `j : W → Z` is a linear isometry with closed range. None of these spaces is assumed complete."
`U ⊆ P` is open.

Paper statement: "For `n ∈ ℕ ∪ {∞}`, a map `f : U → W` is `Cⁿ` if and only if `j f` is `Cⁿ`."

## Formalization notes
* `n : ℕ∞` covers `ℕ ∪ {∞}`; `ω` is excluded, as in the paper.
* `f : U → W` is a total function `f : P → W` with `ContDiffOn K n f U` for open `U`.
-/

open scoped ContDiff

namespace AlternatingAnalyticChallenge.Lem3_2

/-- On an open set, `f` is `Cⁿ` (`n ≤ ∞`) iff `j ∘ f` is, for a linear isometry `j` with closed
range. -/
theorem smooth_descent
    {K : Type*} [NontriviallyNormedField K]
    {P W Z : Type*} [NormedAddCommGroup P] [NormedSpace K P]
    [NormedAddCommGroup W] [NormedSpace K W] [NormedAddCommGroup Z] [NormedSpace K Z]
    (j : W →ₗᵢ[K] Z) (hj : IsClosed (Set.range j))
    {U : Set P} (hU : IsOpen U) (f : P → W) (n : ℕ∞) :
    ContDiffOn K n f U ↔ ContDiffOn K n (j ∘ f) U := by
  sorry

end AlternatingAnalyticChallenge.Lem3_2
