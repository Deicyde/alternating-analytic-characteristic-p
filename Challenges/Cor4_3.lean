import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Analytic.Basic
import AlternatingAnalytic.Analysis.EquivalentUltrametric

/-!
# Corollary 4.3 (discretely valued bases), p. 10

Paper statement (Section 4.1, `cor:discrete-targets`): Suppose `K` is nonarchimedean with
`|K^×| = r^ℤ` for some `0 < r < 1`. Every Banach target `F` admitting an equivalent
nonarchimedean norm makes `A^k_{E,E';F}` analytic in every degree and for all normed `E, E'`.
The field itself need not be complete.

Here `A^k_{E,E';F}(f)(m) = m ∘ (f, …, f)` is precomposition
`L(E,E') → L(Alt^k(E';F), Alt^k(E;F))`.

## Formalization notes
* Degree: the index type is `Fin k`, every `k : ℕ`.
* `K` is a `NontriviallyNormedField` with `IsUltrametricDist K`; the value-group hypothesis
  `|K^×| = r^ℤ` is `Set.range (fun c : Kˣ => ‖(c : K)‖) = Set.range (fun n : ℤ => r ^ n)` with
  `0 < r < 1`. `K` is not assumed complete.
* "Banach target" is `[CompleteSpace F]` for the given norm of `F`; the given norm need not be
  ultrametric.
* "Admitting an equivalent nonarchimedean norm" is the library definition
  `AlternatingAnalytic.HasEquivalentUltrametricNorm K F` (imported from
  `AlternatingAnalytic.Analysis.EquivalentUltrametric` for this definition only): there is a
  seminorm `q` on `F` with `q (x + y) ≤ max (q x) (q y)` and constants `C, C' > 0` with
  `‖x‖ ≤ C q x` and `q x ≤ C' ‖x‖` (the lower bound makes `q` a norm).
* "Analytic" for a map on the whole operator space is `AnalyticAt` at every point.
* `E, E'` are arbitrary normed spaces; no completeness.
-/

namespace AlternatingAnalyticChallenge.Cor4_3

universe uK uE uE' uF

/-- **Corollary 4.3.** Over a nonarchimedean field with value group `r^ℤ`, `0 < r < 1`, a Banach
target `F` with an equivalent nonarchimedean norm makes precomposition on degree-`k` continuous
alternating maps analytic at every point, for all normed `E, E'` and every `k`. -/
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
