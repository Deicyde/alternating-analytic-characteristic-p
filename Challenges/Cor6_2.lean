import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Corollary 6.2 (regularity on whole hom spaces), p. 16

Paper statement: "For every nontrivially normed field K, the bifunctor
Alt^k : Vec_K^op × Vec_K → Vec_K is C^∞, and is analytic if and only if k! ≠ 0 in K. Both
assertions remain true on the full subcategory of Banach spaces."

Here `Vec_K` is the category of normed `K`-spaces and bounded linear maps, and a functor is
`C^n` or analytic when its maps on hom spaces are jointly `C^n` or analytic; products carry the
maximum norm. An arrow `(E, F) → (E', F')` of `Vec^op × Vec` is a pair
`(u, v) ∈ L(E', E) × L(F, F')`, acting by `m ↦ v ∘ m ∘ (u, …, u)`.

## Formalization notes
* The bifunctor is stated in hom coordinates: its joint hom map is `alternatingAction k`,
  `(u, v) ↦ (m ↦ v ∘ m ∘ (u, …, u))` on `L(E', E) × L(F, F')`. Functoriality is not restated.
* The degree is `Fin k`; `k! ≠ 0 in K` is `(k.factorial : K) ≠ 0`.
* "C^∞" is `ContDiff K ∞`, stated for spaces in arbitrary universes.
* "Analytic" is `AnalyticOnNhd K _ Set.univ`; the equivalence quantifies over all spaces in the
  universe of `K`.
* The Banach subcategory is modelled by `CompleteSpace` on all four spaces.
* The paper's "analytic" means the class `C^ω`; the power-series form is stated here. The two
  agree in this case: when `k! ≠ 0` the maps are `CPolynomialAt`, and when `k! = 0` the failure
  of `AnalyticAt` rules out `C^ω`.
-/

open scoped ContDiff

namespace AlternatingAnalyticChallenge.Cor6_2

universe u uE uE' uF uF'

/-- The joint hom map of the bifunctor `Alt^k : Vec^op × Vec → Vec` in coordinates:
`(u, v) ↦ (m ↦ v ∘ m ∘ (u, …, u))`, from `L(E', E) × L(F, F')` to
`L(Alt^k(E; F), Alt^k(E'; F'))`. -/
noncomputable def alternatingAction (K : Type*) [NontriviallyNormedField K]
    {E E' F F' : Type*} [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup E'] [NormedSpace K E'] [NormedAddCommGroup F] [NormedSpace K F]
    [NormedAddCommGroup F'] [NormedSpace K F'] (k : ℕ)
    (h : (E' →L[K] E) × (F →L[K] F')) :
    (E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F') :=
  (ContinuousLinearMap.compContinuousAlternatingMapCLM K E' F F' (Fin k) h.2).comp
    (ContinuousAlternatingMap.compContinuousLinearMapCLM h.1)

/-- Corollary 6.2, smoothness: every joint hom map of `Alt^k` is `C^∞`. -/
theorem alternatingAction_contDiff (K : Type u) [NontriviallyNormedField K] (k : ℕ)
    (E : Type uE) (E' : Type uE') (F : Type uF) (F' : Type uF')
    [NormedAddCommGroup E] [NormedSpace K E] [NormedAddCommGroup E'] [NormedSpace K E']
    [NormedAddCommGroup F] [NormedSpace K F] [NormedAddCommGroup F'] [NormedSpace K F'] :
    ContDiff K ∞ (alternatingAction K (E := E) (E' := E') (F := F) (F' := F') k) := by
  sorry

/-- Corollary 6.2, smoothness on Banach spaces. -/
theorem alternatingAction_contDiff_banach (K : Type u) [NontriviallyNormedField K] (k : ℕ)
    (E : Type uE) (E' : Type uE') (F : Type uF) (F' : Type uF')
    [NormedAddCommGroup E] [NormedSpace K E] [NormedAddCommGroup E'] [NormedSpace K E']
    [NormedAddCommGroup F] [NormedSpace K F] [NormedAddCommGroup F'] [NormedSpace K F']
    [CompleteSpace E] [CompleteSpace E'] [CompleteSpace F] [CompleteSpace F'] :
    ContDiff K ∞ (alternatingAction K (E := E) (E' := E') (F := F) (F' := F') k) := by
  sorry

/-- Corollary 6.2, analyticity: `Alt^k` is analytic on every hom space of `Vec_K^op × Vec_K`
if and only if `k! ≠ 0` in `K`. -/
theorem alternatingAction_analytic_iff (K : Type u) [NontriviallyNormedField K] (k : ℕ) :
    (∀ (E E' F F' : Type u)
      [NormedAddCommGroup E] [NormedSpace K E] [NormedAddCommGroup E'] [NormedSpace K E']
      [NormedAddCommGroup F] [NormedSpace K F] [NormedAddCommGroup F'] [NormedSpace K F'],
      AnalyticOnNhd K (alternatingAction K (E := E) (E' := E') (F := F) (F' := F') k)
        Set.univ) ↔
    (k.factorial : K) ≠ 0 := by
  sorry

/-- Corollary 6.2, analyticity on Banach spaces: the same equivalence for Banach spaces. -/
theorem alternatingAction_analytic_iff_banach (K : Type u) [NontriviallyNormedField K] (k : ℕ) :
    (∀ (E E' F F' : Type u)
      [NormedAddCommGroup E] [NormedSpace K E] [NormedAddCommGroup E'] [NormedSpace K E']
      [NormedAddCommGroup F] [NormedSpace K F] [NormedAddCommGroup F'] [NormedSpace K F']
      [CompleteSpace E] [CompleteSpace E'] [CompleteSpace F] [CompleteSpace F'],
      AnalyticOnNhd K (alternatingAction K (E := E) (E' := E') (F := F) (F' := F') k)
        Set.univ) ↔
    (k.factorial : K) ≠ 0 := by
  sorry

end AlternatingAnalyticChallenge.Cor6_2
