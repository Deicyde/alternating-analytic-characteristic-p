import AlternatingAnalytic.Analysis.SphericalCompleteness
import AlternatingAnalytic.Analysis.DiscreteSphericalCompleteness

/-!
# Lemma D.1 (discrete distances), pp. 40-41

Solution: the statement of `Challenges/LemD_1.lean`, proved from the library theorem
`AlternatingAnalytic.sphericallyCompleteSpace_of_discreteDist_radius`
(`AlternatingAnalytic/Analysis/DiscreteSphericalCompleteness.lean`), whose hypothesis is
`dist x y = r ^ n` for `x ≠ y`.
-/

namespace AlternatingAnalyticChallenge.LemD_1

universe u

/-- **Lemma D.1.** A complete ultrametric space whose distances lie in `r ^ ℤ ∪ {0}` for some
`0 < r < 1` is spherically complete. -/
theorem sphericallyComplete_of_discrete_distances
    {Y : Type u} [MetricSpace Y] [IsUltrametricDist Y] [CompleteSpace Y]
    (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (hdist : ∀ x y : Y, dist x y = 0 ∨ ∃ n : ℤ, dist x y = r ^ n) :
    SphericallyCompleteSpace Y := by
  refine AlternatingAnalytic.sphericallyCompleteSpace_of_discreteDist_radius hr0 hr1 ?_
  intro x y hxy
  rcases hdist x y with h | h
  · exact absurd (dist_eq_zero.mp h) hxy
  · exact h

end AlternatingAnalyticChallenge.LemD_1
