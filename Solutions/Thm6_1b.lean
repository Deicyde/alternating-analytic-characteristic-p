import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Algebra.CharP.Defs
import AlternatingAnalytic.Analysis.SphericalCompleteness
import AlternatingAnalytic.Scalar.ScalarObstruction
import AlternatingAnalytic.Scalar.ChainSpaces.Unconditional

/-!
# Proof of Theorem 6.1(2)

Reduces to Theorem F.1 (`k! = 0` since `p ∣ k!`) through
`ScalarObstruction.exists_nonarchimedean_banach_nowhere_analytic_scalar_of_thmF` and
`ScalarObstruction.exists_nowhere_analytic_scalar_in_bounded_sequences_of_thmF`
(`Scalar/ScalarObstruction.lean`), with `ChainSpaces.abstractConclusion` and
`ChainSpaces.sequenceConclusion` (`Scalar/ChainSpaces/Unconditional.lean`).
-/

open Filter Topology
open scoped ENNReal

set_option maxSynthPendingDepth 2

namespace AlternatingAnalyticChallenge.Thm6_1b

universe u

/-- Theorem 6.1(2): over a complete, not spherically complete `K` of characteristic `p > 0`,
with `k ≥ p`, there are nonarchimedean Banach `E`, `D` with `A^k_{E,D;K}` analytic at no point. -/
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

/-- Theorem 6.1(2), sequence-space form: the witnesses can be chosen as closed subspaces of
`ℓ^∞(Λ, K^{k+1})` and `ℓ^∞(Λ, K^k)` containing the `c_0` spaces, with `Λ` countable. -/
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
