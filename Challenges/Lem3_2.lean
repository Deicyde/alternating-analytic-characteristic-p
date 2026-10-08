import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# Lemma 3.2 (smooth descent), p. 8

Standing assumptions of Section 3: "`K` is nontrivially normed, `P, W, Z` are normed `K`-spaces,
and `j : W → Z` is a linear isometry with closed range. None of these spaces is assumed complete."
`U ⊆ P` is open.

Paper statement: "For `n ∈ ℕ ∪ {∞}`, a map `f : U → W` is `Cⁿ` if and only if `j f` is `Cⁿ`."

Formalization notes:
* `n : ℕ∞` covers `ℕ ∪ {∞}`; the analytic order `ω` is excluded, as in the paper.
* The map `f : U → W` on the open set `U` is modelled as a total function `f : P → W` with
  `ContDiffOn K n _ U` and `IsOpen U`; on an open set `ContDiffOn` is the usual `Cⁿ` notion and
  is insensitive to the values of `f` outside `U`.
* `j` is `W →ₗᵢ[K] Z` with `IsClosed (Set.range j)`. No completeness of `K`, `P`, `W`, `Z`.
* No definitions are introduced.
-/

open scoped ContDiff

namespace AlternatingAnalyticChallenge.Lem3_2

/-- **Lemma 3.2.** On an open set, `f` is `Cⁿ` (`n ≤ ∞`) iff `j ∘ f` is, for a linear isometry `j`
with closed range. -/
theorem smooth_descent
    {K : Type*} [NontriviallyNormedField K]
    {P W Z : Type*} [NormedAddCommGroup P] [NormedSpace K P]
    [NormedAddCommGroup W] [NormedSpace K W] [NormedAddCommGroup Z] [NormedSpace K Z]
    (j : W →ₗᵢ[K] Z) (hj : IsClosed (Set.range j))
    {U : Set P} (hU : IsOpen U) (f : P → W) (n : ℕ∞) :
    ContDiffOn K n f U ↔ ContDiffOn K n (j ∘ f) U := by
  sorry

end AlternatingAnalyticChallenge.Lem3_2
