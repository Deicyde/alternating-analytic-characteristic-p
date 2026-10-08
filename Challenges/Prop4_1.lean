import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Proposition 4.1 (splitting the alternating inclusion), pp. 8-9

Paper statement (Section 4.1, `prop:split-lift`): Let `K` be a nontrivially normed field and
`E, F` normed `K`-spaces. If the inclusion `j_E : Alt^k(E;F) ↪ Mult^k(E;F)` has a bounded linear
retraction `ρ`, then `A^k_{E,E';F}` has a bounded `k`-linear lift of norm at most `‖ρ‖`, for every
normed `E'`. Such a lift also exists in each of the following cases:
1. `k! ≠ 0` in `K`;
2. either `E` or `E'` has a finite algebraic basis with continuous coordinate functionals.
No completeness hypothesis is required.

Here `A^k_{E,E';F} : L(E,E') → L(Alt^k(E';F), Alt^k(E;F))`, `A(f)(m) = m ∘ (f, …, f)` is
precomposition, and a *bounded `k`-linear lift* is a bounded `k`-linear map
`Q : L(E,E')^k → L(Alt^k(E';F), Alt^k(E;F))` whose diagonal is `A` (Proposition 3.3, p. 8).

## Formalization notes
* Degree: the index type is `Fin k`.
* `Alt^k(E;F)` is `E [⋀^Fin k]→L[K] F`, `Mult^k(E;F)` is `E [×k]→L[K] F`, the inclusion `j_E` is
  `ContinuousAlternatingMap.toContinuousMultilinearMap`, and `A^k_{E,E';F}` is
  `ContinuousAlternatingMap.compContinuousLinearMapCLM`.
* A bounded linear retraction of `j_E` is a continuous linear map
  `ρ : (E [×k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F)` with `ρ (j_E m) = m` for all `m`.
* The definition `HasBoundedLift K k E E' F` (introduced here) says that there is a continuous
  `k`-linear map `P : (E →L[K] E')^k → ((E' [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F))` with
  `P (f, …, f) = A f` for every `f`. The library's `Round24Transfer.HasBoundedLift` is the same
  notion indexed by `Fin (Fintype.card ι)`.
* The main part states the norm bound `‖P‖ ≤ ‖ρ‖` in its unfolded, equivalent pointwise form
  `‖P(f₁,…,f_k)(m)(x)‖ ≤ ‖ρ‖ ‖m‖ ∏‖f_i‖ ∏‖x_j‖` (this is exactly the defining property of the
  operator norms involved). The pointwise form is used because Lean does not synthesize the
  `Norm` instance on this iterated operator space automatically. Parts (1) and (2) are stated, as in the paper's statement, as existence of a
  bounded `k`-linear lift; the explicit bounds `k!/|k!|` and `k! ∑_s ∏_a ‖ε_{s_a}‖ ‖e_{s_a}‖`
  appear only in the paper's proof and are not part of these statements.
* "A finite algebraic basis with continuous coordinate functionals" is a Mathlib
  `Basis (Fin d) K E` (resp. `E'`) all of whose coordinate functionals `b.coord i` are
  continuous. Part (2) is split into `part2_domain` (basis of `E`) and `part2_codomain`
  (basis of `E'`).
* No completeness, characteristic or ultrametric hypotheses anywhere.
-/

namespace AlternatingAnalyticChallenge.Prop4_1

universe uK uE uE' uF

/-- Precomposition `A^k_{E,E';F}` has a bounded `k`-linear lift: a continuous `k`-linear map on
`L(E,E')` whose diagonal is `f ↦ (m ↦ m ∘ (f, …, f))`. -/
def HasBoundedLift (K : Type uK) [NontriviallyNormedField K] (k : ℕ)
    (E : Type uE) (E' : Type uE') (F : Type uF)
    [NormedAddCommGroup E] [NormedSpace K E] [NormedAddCommGroup E'] [NormedSpace K E']
    [NormedAddCommGroup F] [NormedSpace K F] : Prop :=
  ∃ P : (E →L[K] E') [×k]→L[K] ((E' [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F)),
    ∀ f : E →L[K] E', P (fun _ => f) = ContinuousAlternatingMap.compContinuousLinearMapCLM f

/-- **Proposition 4.1, main part.** A bounded linear retraction `ρ` of the inclusion
`Alt^k(E;F) ↪ Mult^k(E;F)` gives, for every normed `E'`, a bounded `k`-linear lift of
`A^k_{E,E';F}` of norm at most `‖ρ‖`. -/
theorem lift_of_retraction
    (K : Type uK) [NontriviallyNormedField K] (k : ℕ)
    (E : Type uE) (E' : Type uE') (F : Type uF)
    [NormedAddCommGroup E] [NormedSpace K E] [NormedAddCommGroup E'] [NormedSpace K E']
    [NormedAddCommGroup F] [NormedSpace K F]
    (ρ : (E [×k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F))
    (hρ : ∀ m : E [⋀^Fin k]→L[K] F, ρ m.toContinuousMultilinearMap = m) :
    ∃ P : (E →L[K] E') [×k]→L[K] ((E' [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F)),
      (∀ f : E →L[K] E', P (fun _ => f) = ContinuousAlternatingMap.compContinuousLinearMapCLM f) ∧
      ∀ (f : Fin k → E →L[K] E') (m : E' [⋀^Fin k]→L[K] F) (x : Fin k → E),
        ‖P f m x‖ ≤ ‖ρ‖ * ‖m‖ * (∏ i, ‖f i‖) * ∏ j, ‖x j‖ := by
  sorry

/-- **Proposition 4.1 (1).** If `k! ≠ 0` in `K`, precomposition has a bounded `k`-linear lift. -/
theorem part1
    (K : Type uK) [NontriviallyNormedField K] (k : ℕ)
    (E : Type uE) (E' : Type uE') (F : Type uF)
    [NormedAddCommGroup E] [NormedSpace K E] [NormedAddCommGroup E'] [NormedSpace K E']
    [NormedAddCommGroup F] [NormedSpace K F]
    (hk : (k.factorial : K) ≠ 0) :
    HasBoundedLift K k E E' F := by
  sorry

/-- **Proposition 4.1 (2), coordinates on `E`.** If `E` has a finite algebraic basis with
continuous coordinate functionals, precomposition has a bounded `k`-linear lift. -/
theorem part2_domain
    (K : Type uK) [NontriviallyNormedField K] (k : ℕ)
    (E : Type uE) (E' : Type uE') (F : Type uF)
    [NormedAddCommGroup E] [NormedSpace K E] [NormedAddCommGroup E'] [NormedSpace K E']
    [NormedAddCommGroup F] [NormedSpace K F]
    {d : ℕ} (b : Module.Basis (Fin d) K E) (hb : ∀ i, Continuous (b.coord i)) :
    HasBoundedLift K k E E' F := by
  sorry

/-- **Proposition 4.1 (2), coordinates on `E'`.** If `E'` has a finite algebraic basis with
continuous coordinate functionals, precomposition has a bounded `k`-linear lift. -/
theorem part2_codomain
    (K : Type uK) [NontriviallyNormedField K] (k : ℕ)
    (E : Type uE) (E' : Type uE') (F : Type uF)
    [NormedAddCommGroup E] [NormedSpace K E] [NormedAddCommGroup E'] [NormedSpace K E']
    [NormedAddCommGroup F] [NormedSpace K F]
    {d : ℕ} (b : Module.Basis (Fin d) K E') (hb : ∀ i, Continuous (b.coord i)) :
    HasBoundedLift K k E E' F := by
  sorry

end AlternatingAnalyticChallenge.Prop4_1
