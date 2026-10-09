import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Topology.Bases
import AlternatingAnalytic.Analysis.SphericalCompleteness

/-!
# Theorem F.1 (scalar counterexample), p. 51

Paper statement: "Let K be a complete, nontrivially normed field that is not spherically
complete, and let k ≥ 1 satisfy k! = 0 in K. There are nonarchimedean Banach spaces E, E' for
which
  A^k_{E,E';K} : L(E, E') → L(Alt^k(E'; K), Alt^k(E; K))
is analytic at no point. The spaces may be taken to be closed subspaces of ℓ^∞(Λ; K^{k+1}) and
ℓ^∞(Λ; K^k), respectively, containing the corresponding c_0 spaces, where Λ is countable. Both
spaces are nonseparable."

Here `A^k_{E,E';K}` is precomposition `u ↦ (m ↦ m ∘ (u, …, u))` with the scalar target `K`, and
"analytic" is power-series analyticity (`AnalyticAt`). This is the explicit form of
Theorem 6.1(2).

## Formalization notes

* The hypotheses are the paper's: `[CompleteSpace K]`, `¬ SphericallyCompleteSpace K`, `1 ≤ k`
  and `(k ! : K) = 0`. `SphericallyCompleteSpace` is the library class (every nonempty family of
  pairwise-meeting closed balls has a common point), imported for this definition only.
* `A^k_{E,E';K}` is `ContinuousAlternatingMap.compContinuousLinearMapCLM u :
  (E' [⋀^Fin k]→L[K] K) →L[K] (E [⋀^Fin k]→L[K] K)`.
* `ℓ^∞(Λ; K^n)` is `lp (fun _ : Λ => Fin n → K) ∞` with the max norm on `Fin n → K`. Its `c_0`
  space is the set of elements tending to `0` along the cofinite filter. `E`, `E'` are closed
  submodules; completeness, `IsUltrametricDist` and `¬ SeparableSpace` are stated explicitly.
* `Λ` is a countable type in `Type`. Part 1 is the abstract existence statement (spaces in the
  universe of `K`); part 2 is the sequence-space form with nonseparability, and implies part 1.
* `set_option maxSynthPendingDepth 2` lets Lean find the operator-norm instance on
  `L(Alt^k(E'; K), Alt^k(E; K))` for these submodules.
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
  sorry

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
  sorry

end AlternatingAnalyticChallenge.ThmF_1
