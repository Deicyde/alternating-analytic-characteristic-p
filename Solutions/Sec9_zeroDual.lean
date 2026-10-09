import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Algebra.CharP.Defs
import AlternatingAnalytic.Analysis.SphericalCompleteness
import AlternatingAnalytic.Analysis.UniversalAlternatingTargets
import AlternatingAnalytic.Scalar.ZeroDual
import AlternatingAnalytic.Scalar.ScalarObstruction
import AlternatingAnalytic.Scalar.ChainSpaces.Unconditional

/-!
# Proof of Section 9, universal targets have zero dual

Uses `AlternatingAnalytic.UniversalAlternatingTarget.dual_eq_zero_of_scalar_obstruction`
(`Scalar/ZeroDual.lean`): a nonzero functional makes `K` a retract of `F`, contradicting
Theorem 6.1(2) (`ScalarObstruction.exists_nonarchimedean_banach_nowhere_analytic_scalar_of_thmF`).
-/

namespace AlternatingAnalyticChallenge.Sec9_zeroDual

universe u

/-- Over a complete, non-spherically-complete field of characteristic `p` and in degree
`k ≥ p`, every universal target `F` of `Alt^k(−; F)` has zero continuous dual. -/
theorem universal_target_zero_dual (K : Type u) [NontriviallyNormedField K] [CompleteSpace K]
    (p k : ℕ) (hp : p.Prime) [CharP K p] (hK : ¬ SphericallyCompleteSpace K) (hpk : p ≤ k)
    (F : Type u) [NormedAddCommGroup F] [NormedSpace K F]
    (hF : AlternatingAnalytic.UniversalAlternatingTarget K k F) :
    ∀ l : F →L[K] K, l = 0 := by
  exact hF.dual_eq_zero_of_scalar_obstruction
    (AlternatingAnalytic.ScalarObstruction.exists_nonarchimedean_banach_nowhere_analytic_scalar_of_thmF
      K p k hp.pos hpk hK (fun hK _ hk => AlternatingAnalytic.ChainSpaces.abstractConclusion K hK k hk))

end AlternatingAnalyticChallenge.Sec9_zeroDual
