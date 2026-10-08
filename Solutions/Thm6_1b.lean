import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Algebra.CharP.Defs
import AlternatingAnalytic.Analysis.SphericalCompleteness
import AlternatingAnalytic.Scalar.ScalarObstruction
import AlternatingAnalytic.Scalar.ChainSpaces.Unconditional

/-!
# Theorem 6.1(2) (operator obstructions, scalar target), p. 15

Solution: Theorem 6.1(2) is Theorem F.1 with "characteristic `p > 0`, `k ≥ p`" in place of
"`k ≥ 1`, `k! = 0`". The reduction is
`AlternatingAnalytic.ScalarObstruction.exists_nonarchimedean_banach_nowhere_analytic_scalar_of_thmF`
and `..._in_bounded_sequences_of_thmF` (`Scalar/ScalarObstruction.lean`, using
`factorial_eq_zero_of_charP`: `p ∣ k!`); the Theorem F.1 inputs are
`AlternatingAnalytic.ChainSpaces.abstractConclusion` and `sequenceConclusion`
(`Scalar/ChainSpaces/Unconditional.lean`).
-/

open Filter Topology
open scoped ENNReal

set_option maxSynthPendingDepth 2

namespace AlternatingAnalyticChallenge.Thm6_1b

universe u

/-- **Theorem 6.1(2), abstract form.** Over a complete, not spherically complete normed field of
characteristic `p > 0`, in every degree `k ≥ p`, there are nonarchimedean Banach spaces `E`, `D`
such that scalar precomposition `A^k_{E,D;K}` is analytic at no point of `L(E, D)`. -/
theorem exists_nonarchimedean_banach_nowhere_analytic_scalar
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] (p k : ℕ) [CharP K p]
    (hp : 0 < p) (hpk : p ≤ k) (hK : ¬ SphericallyCompleteSpace K) :
    ∃ (E D : Type u) (_ : NormedAddCommGroup E) (_ : NormedSpace K E) (_ : CompleteSpace E)
      (_ : IsUltrametricDist E)
      (_ : NormedAddCommGroup D) (_ : NormedSpace K D) (_ : CompleteSpace D)
      (_ : IsUltrametricDist D),
      ∀ u₀ : E →L[K] D,
        ¬ AnalyticAt K
          (fun u : E →L[K] D =>
            (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
              (D [⋀^Fin k]→L[K] K) →L[K] (E [⋀^Fin k]→L[K] K))) u₀ := by
  exact AlternatingAnalytic.ScalarObstruction.exists_nonarchimedean_banach_nowhere_analytic_scalar_of_thmF
    K p k hp hpk hK (fun hK _ hk => AlternatingAnalytic.ChainSpaces.abstractConclusion K hK k hk)

/-- **Theorem 6.1(2), sequence-space form.** The witnesses can be chosen as closed subspaces
`E ⊆ ℓ^∞(Λ, K^{k+1})` and `D ⊆ ℓ^∞(Λ, K^k)` containing the corresponding `c_0` spaces, with `Λ`
countable; they are nonarchimedean Banach spaces and `A^k_{E,D;K}` is analytic at no point. -/
theorem exists_nowhere_analytic_scalar_in_bounded_sequences
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] (p k : ℕ) [CharP K p]
    (hp : 0 < p) (hpk : p ≤ k) (hK : ¬ SphericallyCompleteSpace K) :
    ∃ (Λ : Type) (_ : Countable Λ)
      (E : Submodule K (lp (fun _ : Λ => Fin (k + 1) → K) ∞))
      (D : Submodule K (lp (fun _ : Λ => Fin k → K) ∞)),
      IsClosed (E : Set (lp (fun _ : Λ => Fin (k + 1) → K) ∞)) ∧
      IsClosed (D : Set (lp (fun _ : Λ => Fin k → K) ∞)) ∧
      (∀ x : lp (fun _ : Λ => Fin (k + 1) → K) ∞,
        Tendsto (fun i => (x : ∀ _ : Λ, Fin (k + 1) → K) i) cofinite (𝓝 0) → x ∈ E) ∧
      (∀ y : lp (fun _ : Λ => Fin k → K) ∞,
        Tendsto (fun i => (y : ∀ _ : Λ, Fin k → K) i) cofinite (𝓝 0) → y ∈ D) ∧
      CompleteSpace E ∧ CompleteSpace D ∧ IsUltrametricDist E ∧ IsUltrametricDist D ∧
      ∀ u₀ : E →L[K] D,
        ¬ AnalyticAt K
          (fun u : E →L[K] D =>
            (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
              (D [⋀^Fin k]→L[K] K) →L[K] (E [⋀^Fin k]→L[K] K))) u₀ := by
  exact AlternatingAnalytic.ScalarObstruction.exists_nowhere_analytic_scalar_in_bounded_sequences_of_thmF
    K p k hp hpk hK (fun hK _ hk => AlternatingAnalytic.ChainSpaces.sequenceConclusion K hK k hk)

end AlternatingAnalyticChallenge.Thm6_1b
