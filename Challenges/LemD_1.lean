import AlternatingAnalytic.Analysis.SphericalCompleteness

/-!
# Lemma D.1 (discrete distances), pp. 41-42

Paper statement: "Let Y be a complete nonarchimedean space whose distances lie in
r^ℤ ∪ {0} for some r ∈ (0, 1). Then Y is spherically complete."

## Formalization notes
* "Nonarchimedean space" is a metric space with `IsUltrametricDist`.
* "Distances lie in r^ℤ ∪ {0}" is `∀ x y, dist x y = 0 ∨ ∃ n : ℤ, dist x y = r ^ n`.
* Spherical completeness is the library class `SphericallyCompleteSpace`: every nonempty family
  of pairwise meeting closed balls has a common point (as in Theorem 4.2).
-/

namespace AlternatingAnalyticChallenge.LemD_1

universe u

/-- A complete ultrametric space whose distances lie in `r ^ ℤ ∪ {0}` for some
`0 < r < 1` is spherically complete. -/
theorem sphericallyComplete_of_discrete_distances
    {Y : Type u} [MetricSpace Y] [IsUltrametricDist Y] [CompleteSpace Y]
    (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (hdist : ∀ x y : Y, dist x y = 0 ∨ ∃ n : ℤ, dist x y = r ^ n) :
    SphericallyCompleteSpace Y := by
  sorry

end AlternatingAnalyticChallenge.LemD_1
