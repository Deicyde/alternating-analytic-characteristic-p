import AlternatingAnalytic.Analysis.SphericalCompleteness

/-!
# Lemma D.1 (discrete distances), pp. 40-41

Paper statement: "Let Y be a complete nonarchimedean space whose distances lie in
r^ℤ ∪ {0} for some r ∈ (0, 1). Then Y is spherically complete."

Spherical completeness is in the sense of Theorem 4.2: every nonempty family of pairwise
meeting closed balls has a common point.

Formalization notes:
* "Nonarchimedean space" is a metric space with `IsUltrametricDist`; "complete" is
  `CompleteSpace`.
* "Distances lie in r^ℤ ∪ {0}" is `∀ x y, dist x y = 0 ∨ ∃ n : ℤ, dist x y = r ^ n`.
* Spherical completeness is the library class `SphericallyCompleteSpace`
  (`AlternatingAnalytic/Analysis/SphericalCompleteness.lean`): every nonempty family of
  closed balls `closedBall c ρ`, `(c, ρ) ∈ S ⊆ Y × ℝ`, any two of which meet, has a common
  point. That module is imported only for this definition; the proof of the lemma lives in
  `AlternatingAnalytic/Analysis/DiscreteSphericalCompleteness.lean`, which is not imported.
* No definitions are introduced.
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
  sorry

end AlternatingAnalyticChallenge.LemD_1
