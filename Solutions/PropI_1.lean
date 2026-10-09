import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Analytic.Basic
import AlternatingAnalytic.Coordinates.CountableType.Lift

/-!
# Proof of Proposition I.1

The two parts are `CountableType.analyticAt_compContinuousLinearMapCLM_of_countableType_source`
and `_target` (`Coordinates/CountableType/Lift.lean`), built on the sorted lift
`exists_sortedLift_of_countableType` on a space of countable type.
-/

namespace AlternatingAnalyticChallenge.PropI_1

universe uK uE uD uV

/-- A normed space is *of countable type* if some countable subset has dense linear span. -/
def IsOfCountableType (K : Type uK) [NontriviallyNormedField K]
    (V : Type uV) [NormedAddCommGroup V] [NormedSpace K V] : Prop :=
  ∃ S : Set V, S.Countable ∧ Dense (Submodule.span K S : Set V)

/-- Over a complete nonarchimedean field, if `E` is of countable type then `A^k_{E,D;K}` is
analytic at every point. -/
theorem part1
    (K : Type uK) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (E : Type uE) (D : Type uD)
    [NormedAddCommGroup E] [NormedSpace K E] [NormedAddCommGroup D] [NormedSpace K D]
    (hE : IsOfCountableType K E) (k : ℕ) (u₀ : E →L[K] D) :
    AnalyticAt K
      (fun u : E →L[K] D =>
        (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
          (D [⋀^Fin k]→L[K] K) →L[K] (E [⋀^Fin k]→L[K] K))) u₀ :=
  AlternatingAnalytic.CountableType.analyticAt_compContinuousLinearMapCLM_of_countableType_source
    hE k u₀

/-- Over a complete nonarchimedean field, if `D` is of countable type then `A^k_{E,D;K}` is
analytic at every point. -/
theorem part2
    (K : Type uK) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (E : Type uE) (D : Type uD)
    [NormedAddCommGroup E] [NormedSpace K E] [NormedAddCommGroup D] [NormedSpace K D]
    (hD : IsOfCountableType K D) (k : ℕ) (u₀ : E →L[K] D) :
    AnalyticAt K
      (fun u : E →L[K] D =>
        (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
          (D [⋀^Fin k]→L[K] K) →L[K] (E [⋀^Fin k]→L[K] K))) u₀ :=
  AlternatingAnalytic.CountableType.analyticAt_compContinuousLinearMapCLM_of_countableType_target
    hD k u₀

end AlternatingAnalyticChallenge.PropI_1
