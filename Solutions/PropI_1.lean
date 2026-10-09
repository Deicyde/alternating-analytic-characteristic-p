import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Analytic.Basic
import AlternatingAnalytic.Coordinates.CountableType.Lift

/-!
# Proposition I.1 (countable-type scalar sources), pp. 62-63

Solution: the statements of `Challenges/PropI_1.lean`, proved from the library
(`AlternatingAnalytic/Coordinates/CountableType/`):
* `part1`: `analyticAt_compContinuousLinearMapCLM_of_countableType_source` (`Lift.lean`),
  the lift `R_E (m ∘ (u₁, …, u_k))` with `R_E = alternatization ∘ S_E`;
* `part2`: `analyticAt_compContinuousLinearMapCLM_of_countableType_target` (`Lift.lean`),
  the lift `alternatization (S_D m ∘ (u₁, …, u_k))`.
The sorted lift `S` on a space of countable type is `exists_sortedLift_of_countableType`; it uses
the bidual in place of the ultrametric hull (`Hull.lean`), van der Put's basis theorem in
countable-span form (`GramSchmidt.lean`) and the sorted lift on a basis (`SortedLift.lean`).
-/

namespace AlternatingAnalyticChallenge.PropI_1

universe uK uE uD uV

/-- A normed space is *of countable type* if some countable subset has dense linear span. -/
def IsOfCountableType (K : Type uK) [NontriviallyNormedField K]
    (V : Type uV) [NormedAddCommGroup V] [NormedSpace K V] : Prop :=
  ∃ S : Set V, S.Countable ∧ Dense (Submodule.span K S : Set V)

/-- **Proposition I.1, source case.** Over a complete nonarchimedean field, if `E` is of
countable type then precomposition on degree-`k` scalar alternating forms,
`L(E,D) → L(Alt^k(D;K), Alt^k(E;K))`, is analytic at every point, for every `k`. -/
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

/-- **Proposition I.1, target case.** Over a complete nonarchimedean field, if `D` is of
countable type then precomposition on degree-`k` scalar alternating forms,
`L(E,D) → L(Alt^k(D;K), Alt^k(E;K))`, is analytic at every point, for every `k`. -/
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
