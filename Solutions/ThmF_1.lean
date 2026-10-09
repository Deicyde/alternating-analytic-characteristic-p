import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Topology.Bases
import AlternatingAnalytic.Analysis.SphericalCompleteness
import AlternatingAnalytic.Scalar.ChainSpaces.Unconditional

/-!
# Proof of Theorem F.1

Both parts are `ChainSpaces.abstractConclusion` and `ChainSpaces.sequenceConclusion`
(`Scalar/ChainSpaces/Unconditional.lean`), built on the chain spaces of
`Scalar/ChainSpaces/Space.lean` and `not_analyticAt_compContinuousLinearMapCLM` (`NoLift.lean`).
-/

open Filter Topology
open scoped ENNReal

set_option maxSynthPendingDepth 2

namespace AlternatingAnalyticChallenge.ThmF_1

universe u

/-- Theorem F.1, part 1: over a complete field that is not spherically complete, with `k! = 0`,
there are nonarchimedean Banach spaces `E`, `E'` with `A^k_{E,E';K}` analytic at no point. -/
theorem exists_nonarchimedean_banach_nowhere_analytic_scalar
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K]
    (hK : ¬ SphericallyCompleteSpace K) (k : ℕ) (hk1 : 1 ≤ k)
    (hk : (k.factorial : K) = 0) :
    ∃ (E E' : Type u) (_ : NormedAddCommGroup E) (_ : NormedSpace K E) (_ : CompleteSpace E)
      (_ : IsUltrametricDist E)
      (_ : NormedAddCommGroup E') (_ : NormedSpace K E') (_ : CompleteSpace E')
      (_ : IsUltrametricDist E'),
      ∀ u₀ : E →L[K] E',
        ¬ AnalyticAt K
          (fun u : E →L[K] E' =>
            (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
              (E' [⋀^Fin k]→L[K] K) →L[K] (E [⋀^Fin k]→L[K] K))) u₀ := by
  exact AlternatingAnalytic.ChainSpaces.abstractConclusion K hK k hk

/-- Theorem F.1, part 2: the spaces can be taken to be nonseparable closed subspaces
`E ⊆ ℓ^∞(Λ; K^{k+1})` and `E' ⊆ ℓ^∞(Λ; K^k)` containing `c_0`, with `Λ` countable. -/
theorem exists_nowhere_analytic_scalar_in_bounded_sequences
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K]
    (hK : ¬ SphericallyCompleteSpace K) (k : ℕ) (hk1 : 1 ≤ k)
    (hk : (k.factorial : K) = 0) :
    ∃ (Λ : Type) (_ : Countable Λ)
      (E : Submodule K (lp (fun _ : Λ => Fin (k + 1) → K) ∞))
      (E' : Submodule K (lp (fun _ : Λ => Fin k → K) ∞)),
      IsClosed (E : Set (lp (fun _ : Λ => Fin (k + 1) → K) ∞)) ∧
      IsClosed (E' : Set (lp (fun _ : Λ => Fin k → K) ∞)) ∧
      (∀ x : lp (fun _ : Λ => Fin (k + 1) → K) ∞,
        Tendsto (fun i => (x : ∀ _ : Λ, Fin (k + 1) → K) i) cofinite (𝓝 0) → x ∈ E) ∧
      (∀ y : lp (fun _ : Λ => Fin k → K) ∞,
        Tendsto (fun i => (y : ∀ _ : Λ, Fin k → K) i) cofinite (𝓝 0) → y ∈ E') ∧
      CompleteSpace E ∧ CompleteSpace E' ∧ IsUltrametricDist E ∧ IsUltrametricDist E' ∧
      ¬ TopologicalSpace.SeparableSpace E ∧ ¬ TopologicalSpace.SeparableSpace E' ∧
      ∀ u₀ : E →L[K] E',
        ¬ AnalyticAt K
          (fun u : E →L[K] E' =>
            (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
              (E' [⋀^Fin k]→L[K] K) →L[K] (E [⋀^Fin k]→L[K] K))) u₀ := by
  exact AlternatingAnalytic.ChainSpaces.sequenceConclusion K hK k hk

end AlternatingAnalyticChallenge.ThmF_1
