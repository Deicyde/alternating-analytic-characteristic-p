import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Analytic.Basic

/-!
# Proposition I.1 (countable-type scalar sources), pp. 62-63

Paper statement (Appendix I.1, `prop:scalar-countable`): A normed space is *of countable
type* if a countable subset has dense linear span. Let `K` be complete and nonarchimedean.
If either `E` or `D` is of countable type, then `A^k_{E,D;K}` is analytic in every degree.
Neither completeness nor a nonarchimedean norm is required of `E, D`. In particular, the two
spaces in Theorem 6.1(2) (`thm:operator-obstructions`) must both fail to be of countable type.

Here `A^k_{E,D;K}(u)(m) = m ∘ (u, …, u)` is precomposition
`L(E,D) → L(Alt^k(D;K), Alt^k(E;K))` on scalar-valued alternating forms.

## Formalization notes
* Degree: the index type is `Fin k`, for every `k : ℕ` (including `k = 0`).
* `K` is a `NontriviallyNormedField` with `[IsUltrametricDist K]` and `[CompleteSpace K]`.
* `E, D` are arbitrary normed `K`-spaces: neither completeness nor `IsUltrametricDist` is
  assumed.
* "Of countable type" is defined below as `IsOfCountableType K V`: there is a countable set
  `S ⊆ V` whose `K`-linear span is dense in `V`. (Mathlib has no such definition.)
* "Analytic" for a map on the whole operator space `L(E,D)` is `AnalyticAt` at every point.
* The paper's "if either `E` or `D`" is split into two theorems: `part1` (countable-type
  source `E`) and `part2` (countable-type target `D`).
* Omitted: the closing "in particular" sentence, which only applies the proposition to the
  specific spaces of Theorem 6.1(2) (contrapositive); it is not separately stated.
* Imports: Mathlib only; no library module is needed for the statement.
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
          (D [⋀^Fin k]→L[K] K) →L[K] (E [⋀^Fin k]→L[K] K))) u₀ := by
  sorry

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
          (D [⋀^Fin k]→L[K] K) →L[K] (E [⋀^Fin k]→L[K] K))) u₀ := by
  sorry

end AlternatingAnalyticChallenge.PropI_1
