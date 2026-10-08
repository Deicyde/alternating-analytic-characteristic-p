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
* The degree is `Fin k`.
* "Characteristic p > 0" is `[CharP K p]` with `0 < p` (primality of `p` is then automatic).
  The field `K` is not assumed complete, as in the paper.
* `E` and `F` are taken in the same universe as `K`; the paper does not discuss universes.
* `A^k_{E,E;F}` is `ContinuousAlternatingMap.compContinuousLinearMapCLM`.
* "Banach" is `CompleteSpace`.
* "F admits no equivalent nonarchimedean norm" is `¬ AlternatingAnalytic.HasEquivalentUltrametricNorm K F`,
  imported from the library definition module `AlternatingAnalytic.Analysis.EquivalentUltrametric`
  (a `K`-seminorm `q` with `q (x + y) ≤ max (q x) (q y)` and positive constants with
  `‖x‖ ≤ C q x` and `q x ≤ C' ‖x‖`). That module contains only this definition and an
  elementary criterion; it does not prove the claim.
-/

namespace AlternatingAnalyticChallenge.Thm6_1a

universe u

/-- **Theorem 6.1(1).** Over a nontrivially normed field of characteristic `p > 0`, in every
degree `k ≥ p`, there are Banach spaces `E`, `F` such that precomposition
`u ↦ (m ↦ m ∘ (u, …, u))` on `Alt^k(E; F)` is analytic at no point of `L(E, E)`, and `F`
has no equivalent nonarchimedean norm. -/
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
