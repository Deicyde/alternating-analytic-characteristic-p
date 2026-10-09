import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Analytic.Basic

/-!
# Proposition I.1 (countable-type scalar sources), pp. 64-65

Paper statement (Appendix I.1): A normed space is *of countable type* if a countable subset
has dense linear span. Let `K` be complete and nonarchimedean. If either `E` or `D` is of
countable type, then `A^k_{E,D;K}` is analytic in every degree. Neither completeness nor a
nonarchimedean norm is required of `E, D`. In particular, the two spaces in Theorem 6.1(2) must
both fail to be of countable type.

Here `A^k_{E,D;K}(u)(m) = m ∘ (u, …, u)` is precomposition
`L(E,D) → L(Alt^k(D;K), Alt^k(E;K))` on scalar-valued alternating forms.

## Formalization notes
* Degree: index type `Fin k`, for every `k : ℕ`.
* `E, D` are arbitrary normed `K`-spaces, neither complete nor ultrametric.
* "Of countable type" is `IsOfCountableType K V`, defined below (Mathlib has none).
* "Analytic" is `AnalyticAt` at every point of `L(E,D)`.
* `part1` is the case of countable-type `E`, `part2` that of countable-type `D`.
* The closing "in particular" sentence is not stated.
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
          (D [⋀^Fin k]→L[K] K) →L[K] (E [⋀^Fin k]→L[K] K))) u₀ := by
  sorry

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
          (D [⋀^Fin k]→L[K] K) →L[K] (E [⋀^Fin k]→L[K] K))) u₀ := by
  sorry

end AlternatingAnalyticChallenge.PropI_1
