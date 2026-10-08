import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import AlternatingAnalytic.Descent.CoefficientCriterion

/-!
# Theorem 3.1 (the coefficient descent criterion), p. 7

Solution: the statements of `Challenges/Thm3_1.lean`, proved from the library
(`AlternatingAnalytic/Descent/CoefficientCriterion.lean`):
* part 1: `AlternatingAnalytic.CoefficientCriterion.diagonal_mem_range`, from
  `AlternatingAnalytic.HasFPowerSeriesAt.diagonal_mem_closedSubspace`;
* part 2: `AlternatingAnalytic.CoefficientCriterion.analyticAt_iff` (closedness of the range is
  not needed for this part).
-/

namespace AlternatingAnalyticChallenge.Thm3_1

variable {K : Type*} [NontriviallyNormedField K]
  {P W Z : Type*} [NormedAddCommGroup P] [NormedSpace K P]
  [NormedAddCommGroup W] [NormedSpace K W] [NormedAddCommGroup Z] [NormedSpace K Z]

/-- **Theorem 3.1, part 1.** Every diagonal of an ambient expansion lies in `j(W)`. -/
theorem part1 (j : W →ₗᵢ[K] Z) (hj : IsClosed (Set.range j))
    (f : P → W) (x₀ : P) (b : FormalMultilinearSeries K P Z) (R : ℝ) (hR : 0 < R)
    (hbound : BddAbove (Set.range fun n => ‖b n‖ * R ^ n))
    (hexp : ∀ h : P, ‖h‖ < R → HasSum (fun n => b n (fun _ => h)) (j (f (x₀ + h)))) :
    ∀ (n : ℕ) (h : P), b n (fun _ => h) ∈ Set.range j :=
  AlternatingAnalytic.CoefficientCriterion.diagonal_mem_range j hj f x₀ b R hR hbound hexp

/-- **Theorem 3.1, part 2.** `f` is analytic at `x₀` if and only if the ambient diagonals have
`W`-valued bounded multilinear representatives with a positive common radius. -/
theorem part2 (j : W →ₗᵢ[K] Z) (hj : IsClosed (Set.range j))
    (f : P → W) (x₀ : P) (b : FormalMultilinearSeries K P Z) (R : ℝ) (hR : 0 < R)
    (hbound : BddAbove (Set.range fun n => ‖b n‖ * R ^ n))
    (hexp : ∀ h : P, ‖h‖ < R → HasSum (fun n => b n (fun _ => h)) (j (f (x₀ + h)))) :
    AnalyticAt K f x₀ ↔
      ∃ (q : FormalMultilinearSeries K P W) (r : ℝ), 0 < r ∧
        (∀ (n : ℕ) (h : P), j (q n (fun _ => h)) = b n (fun _ => h)) ∧
        BddAbove (Set.range fun n => ‖q n‖ * r ^ n) :=
  AlternatingAnalytic.CoefficientCriterion.analyticAt_iff j f x₀ b R hR hbound hexp

end AlternatingAnalyticChallenge.Thm3_1
