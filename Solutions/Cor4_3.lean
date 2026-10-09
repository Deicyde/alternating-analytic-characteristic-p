import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Analytic.Basic
import AlternatingAnalytic.Analysis.EquivalentUltrametric
import AlternatingAnalytic.Analysis.DiscreteTargetAnalytic

/-!
# Proof of Corollary 4.3

The statement is `AlternatingAnalytic.analyticAt_of_equivalentUltrametricNorm_discreteValueGroup`
(`DiscreteTargetAnalytic.lean`) with index type `Fin k`.
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
  exact AlternatingAnalytic.analyticAt_of_equivalentUltrametricNorm_discreteValueGroup
    (ι := Fin k) hF hr0 hr1 hvalue f₀

end AlternatingAnalyticChallenge.Cor4_3
