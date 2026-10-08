import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.Nat.Factorial.Basic
import AlternatingAnalytic.Analysis.SphericalCompleteness

/-!
# Theorem 6.1(2): the scalar operator obstruction in characteristic `p`

Theorem 6.1(2) of the paper is Theorem F.1 restated with the hypothesis "characteristic `p > 0`,
`k ≥ p`" in place of "`k ≥ 1`, `k! = 0`". This file proves the reduction: in characteristic
`p > 0` with `p ≤ k` one has `1 ≤ k` and `(k ! : K) = 0`, so the two forms of Theorem 6.1(2)
(abstract, and realised in bounded sequence spaces) follow from the corresponding forms of
Theorem F.1. The conclusions of Theorem F.1 are recorded as the propositions
`ThmF1Abstract` and `ThmF1Sequence` and enter as explicit hypotheses.
-/

open Filter Topology
open scoped ENNReal

set_option maxSynthPendingDepth 2

namespace AlternatingAnalytic.ScalarObstruction

universe u

/-- In characteristic `p > 0`, `k!` vanishes as soon as `p ≤ k`. -/
theorem factorial_eq_zero_of_charP (K : Type*) [AddMonoidWithOne K] (p k : ℕ) [CharP K p]
    (hp : 0 < p) (hpk : p ≤ k) : (k.factorial : K) = 0 :=
  (CharP.cast_eq_zero_iff K p _).2 (Nat.dvd_factorial hp hpk)

/-- The conclusion of Theorem F.1, part 1 (abstract form), in degree `k`. -/
def ThmF1Abstract (K : Type u) [NontriviallyNormedField K] (k : ℕ) : Prop :=
  ∃ (E E' : Type u) (_ : NormedAddCommGroup E) (_ : NormedSpace K E) (_ : CompleteSpace E)
    (_ : IsUltrametricDist E)
    (_ : NormedAddCommGroup E') (_ : NormedSpace K E') (_ : CompleteSpace E')
    (_ : IsUltrametricDist E'),
    ∀ u₀ : E →L[K] E',
      ¬ AnalyticAt K
        (fun u : E →L[K] E' =>
          (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
            (E' [⋀^Fin k]→L[K] K) →L[K] (E [⋀^Fin k]→L[K] K))) u₀

/-- The conclusion of Theorem F.1, part 2 (sequence-space form), in degree `k`. -/
def ThmF1Sequence (K : Type u) [NontriviallyNormedField K] (k : ℕ) : Prop :=
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
            (E' [⋀^Fin k]→L[K] K) →L[K] (E [⋀^Fin k]→L[K] K))) u₀

/-- **Theorem 6.1(2), abstract form**, from the abstract form of Theorem F.1. -/
theorem exists_nonarchimedean_banach_nowhere_analytic_scalar_of_thmF
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] (p k : ℕ) [CharP K p]
    (hp : 0 < p) (hpk : p ≤ k) (hK : ¬ SphericallyCompleteSpace K)
    (hF : ¬ SphericallyCompleteSpace K → 1 ≤ k → (k.factorial : K) = 0 → ThmF1Abstract K k) :
    ∃ (E D : Type u) (_ : NormedAddCommGroup E) (_ : NormedSpace K E) (_ : CompleteSpace E)
      (_ : IsUltrametricDist E)
      (_ : NormedAddCommGroup D) (_ : NormedSpace K D) (_ : CompleteSpace D)
      (_ : IsUltrametricDist D),
      ∀ u₀ : E →L[K] D,
        ¬ AnalyticAt K
          (fun u : E →L[K] D =>
            (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
              (D [⋀^Fin k]→L[K] K) →L[K] (E [⋀^Fin k]→L[K] K))) u₀ :=
  hF hK (by omega) (factorial_eq_zero_of_charP K p k hp hpk)

/-- **Theorem 6.1(2), sequence-space form**, from the sequence-space form of Theorem F.1
(forgetting its nonseparability conclusions). -/
theorem exists_nowhere_analytic_scalar_in_bounded_sequences_of_thmF
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] (p k : ℕ) [CharP K p]
    (hp : 0 < p) (hpk : p ≤ k) (hK : ¬ SphericallyCompleteSpace K)
    (hF : ¬ SphericallyCompleteSpace K → 1 ≤ k → (k.factorial : K) = 0 → ThmF1Sequence K k) :
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
  obtain ⟨Λ, hΛ, E, D, hE, hD, hE0, hD0, hEc, hDc, hEu, hDu, -, -, hA⟩ :=
    hF hK (by omega) (factorial_eq_zero_of_charP K p k hp hpk)
  exact ⟨Λ, hΛ, E, D, hE, hD, hE0, hD0, hEc, hDc, hEu, hDu, hA⟩

end AlternatingAnalytic.ScalarObstruction
