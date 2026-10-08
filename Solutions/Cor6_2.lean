import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Data.Nat.Factorial.Basic
import AlternatingAnalytic.Analysis.AlternatingActionRegularity
import AlternatingAnalytic.Analysis.FactorialClassification

/-!
# Corollary 6.2 (regularity on whole hom spaces), p. 15

Solution: `alternatingAction` is definitionally the library's `AlternatingAnalytic.alternatingMapAction`.
Smoothness: `AlternatingAnalytic.contDiff_alternatingMapAction` (`Analysis/AlternatingActionRegularity.lean`).
Analytic iff: the argument of `AlternatingAnalytic.alternatingFunctor_analyticOnHoms_iff`
(`Category/AlternatingRegularity.lean`), i.e. `cpolynomialAt_alternatingMapAction_of_factorial_ne_zero`,
`analyticAt_precomposition_of_analyticAt_alternatingMapAction` and
`factorial_ne_zero_iff_allBanachPrecompositionAnalytic` (`Analysis/FactorialClassification.lean`).
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
  exact AlternatingAnalytic.contDiff_alternatingMapAction k ⊤

/-- **Corollary 6.2, smoothness on Banach spaces.** -/
theorem alternatingAction_contDiff_banach (K : Type u) [NontriviallyNormedField K] (k : ℕ)
    (E : Type uE) (E' : Type uE') (F : Type uF) (F' : Type uF')
    [NormedAddCommGroup E] [NormedSpace K E] [NormedAddCommGroup E'] [NormedSpace K E']
    [NormedAddCommGroup F] [NormedSpace K F] [NormedAddCommGroup F'] [NormedSpace K F']
    [CompleteSpace E] [CompleteSpace E'] [CompleteSpace F] [CompleteSpace F'] :
    ContDiff K ∞ (alternatingAction K (E := E) (E' := E') (F := F) (F' := F') k) := by
  exact AlternatingAnalytic.contDiff_alternatingMapAction k ⊤

/-- **Corollary 6.2, analyticity on `Vec_K`.** The bifunctor `Alt^k` is analytic on every hom
space of `Vec_K^op × Vec_K` if and only if `k! ≠ 0` in `K`. -/
theorem alternatingAction_analytic_iff (K : Type u) [NontriviallyNormedField K] (k : ℕ) :
    (∀ (E E' F F' : Type u)
      [NormedAddCommGroup E] [NormedSpace K E] [NormedAddCommGroup E'] [NormedSpace K E']
      [NormedAddCommGroup F] [NormedSpace K F] [NormedAddCommGroup F'] [NormedSpace K F'],
      AnalyticOnNhd K (alternatingAction K (E := E) (E' := E') (F := F) (F' := F') k)
        Set.univ) ↔
    (k.factorial : K) ≠ 0 := by
  constructor
  · intro h
    apply (AlternatingAnalytic.factorial_ne_zero_iff_allBanachPrecompositionAnalytic K k).2
    intro E E' F _ _ _ _ _ _ _ _ _ u₀
    apply AlternatingAnalytic.analyticAt_precomposition_of_analyticAt_alternatingMapAction k u₀
    exact h E' E F F (u₀, ContinuousLinearMap.id K F) (Set.mem_univ _)
  · intro hk E E' F F' _ _ _ _ _ _ _ _ z _
    exact (AlternatingAnalytic.cpolynomialAt_alternatingMapAction_of_factorial_ne_zero k hk
      z).analyticAt

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
  constructor
  · intro h
    apply (AlternatingAnalytic.factorial_ne_zero_iff_allBanachPrecompositionAnalytic K k).2
    intro E E' F _ _ _ _ _ _ _ _ _ u₀
    apply AlternatingAnalytic.analyticAt_precomposition_of_analyticAt_alternatingMapAction k u₀
    exact h E' E F F (u₀, ContinuousLinearMap.id K F) (Set.mem_univ _)
  · intro hk E E' F F' _ _ _ _ _ _ _ _ _ _ _ _ z _
    exact (AlternatingAnalytic.cpolynomialAt_alternatingMapAction_of_factorial_ne_zero k hk
      z).analyticAt

end AlternatingAnalyticChallenge.Cor6_2
