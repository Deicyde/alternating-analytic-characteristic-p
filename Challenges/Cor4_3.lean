import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Analytic.Basic
import AlternatingAnalytic.Analysis.EquivalentUltrametric

/-!
# Corollary 4.3 (discretely valued bases), p. 10

Paper statement (Section 4.1): "Suppose `K` is nonarchimedean with `|K^×| = r^ℤ` for some
`0 < r < 1`. Every Banach target `F` admitting an equivalent nonarchimedean norm makes
`A^k_{E,E';F}` analytic in every degree and for all normed `E, E'`. The field itself need not be
complete."

Here `A^k_{E,E';F}(f)(m) = m ∘ (f, …, f)` is precomposition
`L(E,E') → L(Alt^k(E';F), Alt^k(E;F))`.

## Formalization notes
* `|K^×| = r^ℤ` is `Set.range (fun c : Kˣ => ‖(c : K)‖) = Set.range (fun n : ℤ => r ^ n)`.
* "Banach target" is `[CompleteSpace F]` for the given norm of `F`, which need not be
  ultrametric.
* "Admitting an equivalent nonarchimedean norm" is `AlternatingAnalytic.HasEquivalentUltrametricNorm`
  (imported for this definition only): a seminorm `q` with `q (x + y) ≤ max (q x) (q y)`,
  `‖x‖ ≤ C q x` and `q x ≤ C' ‖x‖`.
* "Analytic" is `AnalyticAt` at every point `f₀`.
-/

namespace AlternatingAnalyticChallenge.Cor4_3

universe uK uE uE' uF

/-- Over a nonarchimedean field with value group `r^ℤ`, `0 < r < 1`, precomposition
`A^k_{E,E';F}` is analytic at every point when `F` is Banach with an equivalent nonarchimedean
norm. -/
theorem analyticAt_compContinuousLinearMapCLM_of_discreteValueGroup
    (K : Type uK) [NontriviallyNormedField K] [IsUltrametricDist K]
    (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (hvalue : Set.range (fun c : Kˣ => ‖(c : K)‖) = Set.range (fun n : ℤ => r ^ n))
    (E : Type uE) (E' : Type uE') (F : Type uF)
    [NormedAddCommGroup E] [NormedSpace K E] [NormedAddCommGroup E'] [NormedSpace K E']
    [NormedAddCommGroup F] [NormedSpace K F] [CompleteSpace F]
    (hF : AlternatingAnalytic.HasEquivalentUltrametricNorm K F)
    (k : ℕ) (f₀ : E →L[K] E') :
    AnalyticAt K
      (fun f : E →L[K] E' =>
        (ContinuousAlternatingMap.compContinuousLinearMapCLM f :
          (E' [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F))) f₀ := by
  sorry

end AlternatingAnalyticChallenge.Cor4_3
