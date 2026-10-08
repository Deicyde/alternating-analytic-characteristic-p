import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Topology.Bases
import AlternatingAnalytic.Analysis.SphericalCompleteness
import AlternatingAnalytic.Scalar.ChainSpaces.Unconditional

/-!
# Theorem F.1 (scalar counterexample), pp. 48-53

Solution: both parts are `AlternatingAnalytic.ChainSpaces.abstractConclusion` and
`AlternatingAnalytic.ChainSpaces.sequenceConclusion` (`Scalar/ChainSpaces/Unconditional.lean`).
The witnesses are the chain-limit spaces `chainSpace ρ ⊆ ℓ^∞(List (Fin N); K^{k+1})` and
`chainSpace ρ' ⊆ ℓ^∞(List (Fin N); K^k)` (`Scalar/ChainSpaces/Space.lean`), labelled by an
enumeration of the finite family (F.2) (`Family.lean`, `Main.lean`). Nowhere analyticity is
`not_analyticAt_compContinuousLinearMapCLM` (`NoLift.lean`): fibre maps (`FibreMap.lean`), chain
decay through the `(2k+1)`-linear form `Φ` (`ChainDecay.lean`, `ChainForm.lean`, `Operators.lean`),
the chain gap lemma (`Scalar/ChainGap.lean`), the multilinear tail property (`Scalar/Tails/`), the
finite test certificate (`Scalar/TestCertificate/`, from `Scalar/FibreObstruction.lean`) and the
lift criterion `Round24Transfer.hasBoundedLift_of_analyticAt`. The hypothesis `1 ≤ k` is not used
(`k! = 0` already forces `k ≥ 2`).
-/

open Filter Topology
open scoped ENNReal

set_option maxSynthPendingDepth 2

namespace AlternatingAnalyticChallenge.ThmF_1

universe u

/-- **Theorem F.1, part 1 (abstract form).** Over a complete, nontrivially normed, not spherically
complete field with `k! = 0`, `k ≥ 1`, there are nonarchimedean Banach spaces `E`, `E'` such that
scalar precomposition `A^k_{E,E';K}` is analytic at no point of `L(E, E')`. -/
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

/-- **Theorem F.1, part 2 (sequence-space form).** The witnesses can be chosen as closed subspaces
`E ⊆ ℓ^∞(Λ; K^{k+1})` and `E' ⊆ ℓ^∞(Λ; K^k)` containing the corresponding `c_0` spaces, with `Λ`
countable; they are nonseparable nonarchimedean Banach spaces and `A^k_{E,E';K}` is analytic at no
point. -/
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
