import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Algebra.CharP.Defs
import AlternatingAnalytic.Analysis.EquivalentUltrametric

/-!
# Theorem 6.1(1) (operator obstructions, Banach target), p. 15

Paper statement: "Let K be a nontrivially normed field of characteristic p > 0, and let
k ≥ p. (1) There are Banach K-spaces E, F for which
A^k_{E,E;F} : L(E, E) → L(Alt^k(E; F), Alt^k(E; F)) is analytic at no point. The target F
admits no equivalent nonarchimedean norm."

Here `A^k_{E,E;F}(u)` is precomposition `m ↦ m ∘ (u, …, u)`, and "analytic" is
power-series analyticity (Mathlib `AnalyticAt`).

## Formalization notes
* The degree is `Fin k`. "Characteristic p > 0" is `[CharP K p]` with `0 < p`. `K` is not
  assumed complete.
* `E` and `F` live in the universe of `K`.
* `A^k_{E,E;F}` is `ContinuousAlternatingMap.compContinuousLinearMapCLM`; "Banach" is
  `CompleteSpace`.
* "No equivalent nonarchimedean norm" is `¬ HasEquivalentUltrametricNorm K F`, from the
  definition file `Analysis/EquivalentUltrametric.lean`: a seminorm with the strong triangle
  inequality, two-sided equivalent to the norm.
-/

namespace AlternatingAnalyticChallenge.Thm6_1a

universe u

/-- Theorem 6.1(1): in characteristic `p > 0` and degree `k ≥ p` there are Banach `E`, `F`
with `A^k_{E,E;F}` analytic at no point and `F` without an equivalent nonarchimedean norm. -/
theorem exists_banach_nowhere_analytic_precomposition
    (K : Type u) [NontriviallyNormedField K] (p k : ℕ) [CharP K p] (hp : 0 < p)
    (hpk : p ≤ k) :
    ∃ (E F : Type u) (_ : NormedAddCommGroup E) (_ : NormedSpace K E) (_ : CompleteSpace E)
      (_ : NormedAddCommGroup F) (_ : NormedSpace K F) (_ : CompleteSpace F),
      (∀ u₀ : E →L[K] E,
        ¬ AnalyticAt K
          (fun u : E →L[K] E =>
            (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
              (E [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F))) u₀) ∧
      ¬ AlternatingAnalytic.HasEquivalentUltrametricNorm K F := by
  sorry

end AlternatingAnalyticChallenge.Thm6_1a
