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
* "Complete" is `[CompleteSpace K]`; "not spherically complete" is
  `¬ SphericallyCompleteSpace K`, using the library class `SphericallyCompleteSpace`
  (every nonempty family of pairwise-meeting closed balls has a common point), imported from
  `AlternatingAnalytic.Analysis.SphericalCompleteness`, which defines the class and proves
  positive (extension) results only. No nonarchimedean hypothesis on `K` is added: every
  normed field of positive characteristic is nonarchimedean (paper, Conventions).
* `ℓ^∞(Λ, K^n)` is Mathlib's `lp (fun _ : Λ => Fin n → K) ∞`, where `Fin n → K` carries the
  maximum norm. The corresponding `c_0` space is the set of its elements tending to `0` along
  the cofinite filter; "containing c_0" is stated as membership of all such elements.
* `E`, `D` are closed `K`-submodules of the sequence spaces, with the induced norms. That they
  are complete and nonarchimedean (`IsUltrametricDist`) is stated explicitly, as in the paper's
  wording, although it follows from closedness in `ℓ^∞`.
* `set_option maxSynthPendingDepth 2` is needed so that Lean finds the operator-norm instance
  on `L(Alt^k(D; K), Alt^k(E; K))` for these submodules; it changes no definition.
* `Λ` is a countable type in `Type`; `E`, `D` lie in the universe of `K`.
  `Countable Λ` also allows a finite `Λ`, while the paper's construction uses an infinite tree.
  This does not weaken the claim: a finite `Λ` gives finite-dimensional `E`, `D`, where the
  action is analytic by the finite-coordinate results, so any witness has `Λ` infinite. The first theorem is
  the main existence statement; the second adds the paper's sequence-space realisation and
  implies the first. Both are listed so that the main claim can be checked on its own.
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
  sorry

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
  sorry

end AlternatingAnalyticChallenge.Thm6_1b
