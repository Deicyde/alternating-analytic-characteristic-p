import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import AlternatingAnalytic.Descent.SmoothDescentOn

/-!
# Lemma 3.2 (smooth descent), p. 8

Solution: the statement of `Challenges/Lem3_2.lean`, proved by
`AlternatingAnalytic.contDiffOn_iff_comp_linearIsometry` (`Descent/SmoothDescentOn.lean`), the
open-set induction on the order through `LinearIsometry.postcomp`.
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
    ContDiffOn K n f U ↔ ContDiffOn K n (j ∘ f) U :=
  AlternatingAnalytic.contDiffOn_iff_comp_linearIsometry j hj hU f n

end AlternatingAnalyticChallenge.Lem3_2
