import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Data.Nat.Factorial.Basic
import AlternatingAnalytic.Analysis.SphericalCompleteness
import AlternatingAnalytic.Scalar.ScalarClassification.Unconditional

/-!
# Theorem 6.3 (universal scalar classification), p. 16

Solution: the "if" direction is
`AlternatingAnalytic.ScalarClassification.analyticOnNhd_of_factorial_ne_zero_or_sphericallyComplete`
(`Scalar/ScalarClassification.lean`: the factorial-invertible case from `FactorialInvertible.lean`
and the spherically complete case from `SphericalAnalytic.lean`). The three equivalences are
`analytic_on_homs_iff'`, `analytic_on_homs_iff_banach'` and
`analytic_on_homs_iff_nonarchimedean_banach'` (`Scalar/ScalarClassification/Unconditional.lean`),
whose "only if" halves use Theorem 6.1(2) (`scalarObstruction`): `k! = 0` in `K` forces
`char K = p` prime with `p ≤ k`.
-/

namespace AlternatingAnalyticChallenge.Thm6_3

universe u

/-- **Theorem 6.3, "if" direction, arbitrary normed sources.** If `k! ≠ 0` in `K` or `K` is
spherically complete, scalar pullback `u ↦ u^*` on `Alt^k(−; K)` is analytic on every Hom
space. -/
theorem analyticOnNhd_of_factorial_ne_zero_or_sphericallyComplete
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] (k : ℕ)
    (h : (k.factorial : K) ≠ 0 ∨ SphericallyCompleteSpace K)
    (E D : Type u) [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup D] [NormedSpace K D] :
    AnalyticOnNhd K
      (fun u : E →L[K] D =>
        (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
          (D [⋀^Fin k]→L[K] K) →L[K] (E [⋀^Fin k]→L[K] K))) Set.univ := by
  exact AlternatingAnalytic.ScalarClassification.analyticOnNhd_of_factorial_ne_zero_or_sphericallyComplete
    K k h E D

/-- **Theorem 6.3, normed sources.** `Alt^k(−; K)` on `Vec_K^op` is analytic on every Hom space
if and only if `k! ≠ 0` in `K` or `K` is spherically complete. -/
theorem analytic_on_homs_iff
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] (k : ℕ) :
    (∀ (E D : Type u) [NormedAddCommGroup E] [NormedSpace K E]
      [NormedAddCommGroup D] [NormedSpace K D],
      AnalyticOnNhd K
        (fun u : E →L[K] D =>
          (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
            (D [⋀^Fin k]→L[K] K) →L[K] (E [⋀^Fin k]→L[K] K))) Set.univ) ↔
    ((k.factorial : K) ≠ 0 ∨ SphericallyCompleteSpace K) := by
  exact AlternatingAnalytic.ScalarClassification.analytic_on_homs_iff' K k

/-- **Theorem 6.3, Banach sources.** The same equivalence for Banach source spaces. -/
theorem analytic_on_homs_iff_banach
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] (k : ℕ) :
    (∀ (E D : Type u) [NormedAddCommGroup E] [NormedSpace K E] [CompleteSpace E]
      [NormedAddCommGroup D] [NormedSpace K D] [CompleteSpace D],
      AnalyticOnNhd K
        (fun u : E →L[K] D =>
          (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
            (D [⋀^Fin k]→L[K] K) →L[K] (E [⋀^Fin k]→L[K] K))) Set.univ) ↔
    ((k.factorial : K) ≠ 0 ∨ SphericallyCompleteSpace K) := by
  exact AlternatingAnalytic.ScalarClassification.analytic_on_homs_iff_banach' K k

/-- **Theorem 6.3, nonarchimedean Banach sources.** The same equivalence for nonarchimedean
Banach source spaces. -/
theorem analytic_on_homs_iff_nonarchimedean_banach
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] (k : ℕ) :
    (∀ (E D : Type u) [NormedAddCommGroup E] [NormedSpace K E] [CompleteSpace E]
      [IsUltrametricDist E] [NormedAddCommGroup D] [NormedSpace K D] [CompleteSpace D]
      [IsUltrametricDist D],
      AnalyticOnNhd K
        (fun u : E →L[K] D =>
          (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
            (D [⋀^Fin k]→L[K] K) →L[K] (E [⋀^Fin k]→L[K] K))) Set.univ) ↔
    ((k.factorial : K) ≠ 0 ∨ SphericallyCompleteSpace K) := by
  exact AlternatingAnalytic.ScalarClassification.analytic_on_homs_iff_nonarchimedean_banach' K k

end AlternatingAnalyticChallenge.Thm6_3
