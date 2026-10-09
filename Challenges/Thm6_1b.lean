import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Algebra.CharP.Defs
import AlternatingAnalytic.Analysis.SphericalCompleteness

/-!
# Theorem 6.1(2) (operator obstructions, scalar target), p. 15

Paper statement: "Let K be a nontrivially normed field of characteristic p > 0, and let
k ≥ p. [...] (2) If K is complete and not spherically complete, there are nonarchimedean
Banach spaces E, D for which A^k_{E,D;K} is analytic at no point. They can be chosen as closed
subspaces of ℓ^∞(Λ, K^{k+1}) and ℓ^∞(Λ, K^k), respectively, containing the corresponding c_0
spaces, with Λ countable."

Here `A^k_{E,D;K} : L(E, D) → L(Alt^k(D; K), Alt^k(E; K))` is precomposition
`u ↦ (m ↦ m ∘ (u, …, u))` with the scalar target `K`, and "analytic" is power-series
analyticity (`AnalyticAt`).

## Formalization notes
* The degree is `Fin k`. "Characteristic p > 0" is `[CharP K p]` with `0 < p`.
* "Not spherically complete" is `¬ SphericallyCompleteSpace K`, a class defined in
  `Analysis/SphericalCompleteness.lean`. `K` is nonarchimedean automatically in positive
  characteristic, so no such hypothesis is added.
* `ℓ^∞(Λ, K^n)` is `lp (fun _ : Λ => Fin n → K) ∞` with the maximum norm on `Fin n → K`;
  "containing `c_0`" means every element tending to `0` along the cofinite filter lies in it.
* `E`, `D` are closed submodules with the induced norms; completeness and `IsUltrametricDist`
  are stated explicitly, though they follow.
* `set_option maxSynthPendingDepth 2` lets Lean find the norm instance on
  `L(Alt^k(D; K), Alt^k(E; K))`.
* `Λ : Type` is countable, possibly finite; a finite `Λ` cannot give a witness, since the
  action is then analytic.
* The first theorem is the existence statement; the second adds the sequence-space form.
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
  sorry

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
  sorry

end AlternatingAnalyticChallenge.Thm6_1b
