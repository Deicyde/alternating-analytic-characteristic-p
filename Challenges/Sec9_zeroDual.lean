import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Algebra.CharP.Defs
import AlternatingAnalytic.Analysis.SphericalCompleteness
import AlternatingAnalytic.Analysis.UniversalAlternatingTargets

/-!
# Section 9, "Which fibers remove the obstruction?" (universal targets have zero dual), p. 23

Paper statement (Section 9, in the obstructed range `char K = p > 0`, `k ≥ p`): Call `F` a
universal target if `Alt^k(−; F)` is analytic on every hom space. [...] Over a complete
nonspherically complete field, however, every universal target must have zero continuous dual.
Indeed, if `λ(v) = 1` for `λ ∈ F*` and `v ∈ F`, then
`A^k_{E,D;K}(u)(a) = λ ∘ A^k_{E,D;F}(u)(v a)`. The scalar counterexample (Theorem 6.1(2))
excludes analyticity of the right-hand action.

## Formalization notes
* Degree: index type `Fin k`. Characteristic: `p` prime with `[CharP K p]`, `p ≤ k`.
  `K` is a `NontriviallyNormedField` with `[CompleteSpace K]` and `¬ SphericallyCompleteSpace K`
  (library class, `AlternatingAnalytic/Analysis/SphericalCompleteness.lean`, imported for the
  definition only).
* "Universal target" is the library definition `AlternatingAnalytic.UniversalAlternatingTarget K k
  F` (`AlternatingAnalytic/Analysis/UniversalAlternatingTargets.lean`, imported for this
  definition): for all normed spaces `E, D` in the universe of `K`, the precomposition map
  `u ↦ u^* : L(E, D) → L(Alt^k(D; F), Alt^k(E; F))` is `AnalyticOnNhd` on all of `L(E, D)`.
  This is "analytic on every hom space" of the functor `Alt^k(−; F)` on `NormedSpaceCat K`
  (carriers in the universe of `K`); `F` is also taken in that universe. That module contains
  the retract-transfer lemma `UniversalAlternatingTarget.of_retract` (the compression step) but
  not the scalar counterexample, so it does not prove this claim.
* "Zero continuous dual" is `∀ λ : F →L[K] K, λ = 0`.
* The proof depends on Theorem 6.1(2) (scalar counterexample), which is not in the library.
-/

namespace AlternatingAnalyticChallenge.Sec9_zeroDual

universe u

/-- **Section 9.** Over a complete, non-spherically-complete field of characteristic `p` and in
degree `k ≥ p`, every universal target `F` of `Alt^k(−; F)` has zero continuous dual. -/
theorem universal_target_zero_dual (K : Type u) [NontriviallyNormedField K] [CompleteSpace K]
    (p k : ℕ) (hp : p.Prime) [CharP K p] (hK : ¬ SphericallyCompleteSpace K) (hpk : p ≤ k)
    (F : Type u) [NormedAddCommGroup F] [NormedSpace K F]
    (hF : AlternatingAnalytic.UniversalAlternatingTarget K k F) :
    ∀ l : F →L[K] K, l = 0 := by
  sorry

end AlternatingAnalyticChallenge.Sec9_zeroDual
