import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Corollary 6.2 (regularity on whole hom spaces), p. 15

Paper statement: "For every nontrivially normed field K, the bifunctor
Alt^k : Vec_K^op × Vec_K → Vec_K is C^∞, and is analytic if and only if k! ≠ 0 in K. Both
assertions remain true on the full subcategory of Banach spaces."

Here `Vec_K` is the category of normed `K`-spaces and bounded linear maps (no completeness),
and a functor is `C^n` / analytic when all its maps on (products of) hom spaces are jointly
`C^n` / analytic; products carry the maximum norm (paper, §1–2). An arrow
`(E, F) → (E', F')` of `Vec^op × Vec` is a pair `(u, v) ∈ L(E', E) × L(F, F')`, and it acts
by `m ↦ v ∘ m ∘ (u, …, u)`.

## Formalization notes
* The bifunctor is stated in hom coordinates: the joint hom map is `alternatingAction k`,
  defined below as `(u, v) ↦ (m ↦ v ∘ m ∘ (u, …, u))` on
  `L(E', E) × L(F, F')` (Mathlib's product norm is the maximum norm, as in the paper).
  Functoriality itself is not restated. This definition coincides with the library's
  `AlternatingAnalytic.alternatingMapAction`, but is written here directly in Mathlib terms.
* The degree is `Fin k`.
* "C^∞" is `ContDiff K ∞` on the whole hom space. The smoothness statements are made for spaces
  in arbitrary universes (this is stronger than a statement about one category `Vec_K`).
* "Analytic" is power-series analyticity on the whole hom space: `AnalyticOnNhd K _ Set.univ`
  for all objects. Because the equivalence quantifies over all objects, these objects are taken
  in the universe of `K` (the categories `Vec_K`, `Ban_K` of `K`-spaces in `Type u`).
* The Banach subcategory is expressed by adding `CompleteSpace` for all four objects.
  `alternatingAction_contDiff_banach` is a special case of `alternatingAction_contDiff`; it is
  kept only to mirror the paper's sentence about the Banach subcategory.
* The paper's §2 convention reads "analytic" for a functor as the `C^ω` class, which it does
  not identify with having a power series at each point in general. The power-series form
  (`AnalyticOnNhd`) is stated here. In this case the two readings agree: when `k! ≠ 0` the hom
  maps are `CPolynomialAt`, hence `ContDiff K ω`; when `k! = 0` the failure is `¬ AnalyticAt`,
  which rules out `ContDiffAt K ω` (in Mathlib `ContDiffAt ω` implies `AnalyticAt`). The `C^ω`
  form is not stated.
* `k! ≠ 0 in K` is `(k.factorial : K) ≠ 0`.
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

/-- **Corollary 6.2, smoothness on `Vec_K`.** Every joint hom map of `Alt^k` is `C^∞`. -/
theorem alternatingAction_contDiff (K : Type u) [NontriviallyNormedField K] (k : ℕ)
    (E : Type uE) (E' : Type uE') (F : Type uF) (F' : Type uF')
    [NormedAddCommGroup E] [NormedSpace K E] [NormedAddCommGroup E'] [NormedSpace K E']
    [NormedAddCommGroup F] [NormedSpace K F] [NormedAddCommGroup F'] [NormedSpace K F'] :
    ContDiff K ∞ (alternatingAction K (E := E) (E' := E') (F := F) (F' := F') k) := by
  sorry

/-- **Corollary 6.2, smoothness on Banach spaces.** -/
theorem alternatingAction_contDiff_banach (K : Type u) [NontriviallyNormedField K] (k : ℕ)
    (E : Type uE) (E' : Type uE') (F : Type uF) (F' : Type uF')
    [NormedAddCommGroup E] [NormedSpace K E] [NormedAddCommGroup E'] [NormedSpace K E']
    [NormedAddCommGroup F] [NormedSpace K F] [NormedAddCommGroup F'] [NormedSpace K F']
    [CompleteSpace E] [CompleteSpace E'] [CompleteSpace F] [CompleteSpace F'] :
    ContDiff K ∞ (alternatingAction K (E := E) (E' := E') (F := F) (F' := F') k) := by
  sorry

/-- **Corollary 6.2, analyticity on `Vec_K`.** The bifunctor `Alt^k` is analytic on every hom
space of `Vec_K^op × Vec_K` if and only if `k! ≠ 0` in `K`. -/
theorem alternatingAction_analytic_iff (K : Type u) [NontriviallyNormedField K] (k : ℕ) :
    (∀ (E E' F F' : Type u)
      [NormedAddCommGroup E] [NormedSpace K E] [NormedAddCommGroup E'] [NormedSpace K E']
      [NormedAddCommGroup F] [NormedSpace K F] [NormedAddCommGroup F'] [NormedSpace K F'],
      AnalyticOnNhd K (alternatingAction K (E := E) (E' := E') (F := F) (F' := F') k)
        Set.univ) ↔
    (k.factorial : K) ≠ 0 := by
  sorry

/-- **Corollary 6.2, analyticity on Banach spaces.** The same equivalence on the full
subcategory of Banach spaces. -/
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
