import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Proposition 4.1 (splitting the alternating inclusion), pp. 8-9

Setting: `K` is a nontrivially normed field and `E, E', F` are normed `K`-spaces.

Paper statement (Section 4.1): "If the inclusion `j_{E,F} : Alt^k(E;F) ↪ Mult^k(E;F)` has a bounded
linear retraction `ρ`, then `A^k_{E,E';F}` has a bounded `k`-linear lift of norm at most `‖ρ‖`,
for every normed `E'`. Such a lift also exists in each of the following cases:
1. `k! ≠ 0` in `K`;
2. either `E` or `E'` has a finite algebraic basis with continuous coordinate functionals.
No completeness hypothesis is required."

Here `A^k_{E,E';F}(f)(m) = m ∘ (f, …, f)` is precomposition, and a bounded `k`-linear lift is a
bounded `k`-linear map `Q : L(E,E')^k → L(Alt^k(E';F), Alt^k(E;F))` whose diagonal is `A`.

## Formalization notes
* `Alt^k(E;F)` is `E [⋀^Fin k]→L[K] F`, `Mult^k(E;F)` is `E [×k]→L[K] F`, `j_{E,F}` is
  `toContinuousMultilinearMap`, and `A^k_{E,E';F}` is
  `ContinuousAlternatingMap.compContinuousLinearMapCLM`.
* The bound `‖P‖ ≤ ‖ρ‖` is stated in the equivalent pointwise form
  `‖P(f₁,…,f_k)(m)(x)‖ ≤ ‖ρ‖ ‖m‖ ∏‖f_i‖ ∏‖x_j‖`, because Lean does not find the `Norm` instance
  on this iterated operator space.
* Parts (1) and (2) state existence only; the explicit bounds in the proof are not stated.
* A finite algebraic basis with continuous coordinate functionals is a `Basis (Fin d) K E` whose
  functionals `b.coord i` are continuous. Part (2) is split into `part2_domain` and
  `part2_codomain`.
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

/-- A bounded linear retraction `ρ` of the inclusion
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

/-- If `k! ≠ 0` in `K`, precomposition has a bounded `k`-linear lift. -/
theorem part1
    (K : Type uK) [NontriviallyNormedField K] (k : ℕ)
    (E : Type uE) (E' : Type uE') (F : Type uF)
    [NormedAddCommGroup E] [NormedSpace K E] [NormedAddCommGroup E'] [NormedSpace K E']
    [NormedAddCommGroup F] [NormedSpace K F]
    (hk : (k.factorial : K) ≠ 0) :
    HasBoundedLift K k E E' F := by
  sorry

/-- If `E` has a finite algebraic basis with
continuous coordinate functionals, precomposition has a bounded `k`-linear lift. -/
theorem part2_domain
    (K : Type uK) [NontriviallyNormedField K] (k : ℕ)
    (E : Type uE) (E' : Type uE') (F : Type uF)
    [NormedAddCommGroup E] [NormedSpace K E] [NormedAddCommGroup E'] [NormedSpace K E']
    [NormedAddCommGroup F] [NormedSpace K F]
    {d : ℕ} (b : Module.Basis (Fin d) K E) (hb : ∀ i, Continuous (b.coord i)) :
    HasBoundedLift K k E E' F := by
  sorry

/-- If `E'` has a finite algebraic basis with
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
