import AlternatingAnalytic.Analysis.BaseChangeLiftDescent
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Analytic.Basic

/-!
# Proposition D.9 (descent of a lift), p. 46

Solution: the statements of `Challenges/PropD_9.lean`, proved from
`AlternatingAnalytic/Analysis/BaseChangeLiftDescent.lean`
(`exists_baseChangeLiftDescent`, `not_analyticAt_completedBaseChange_of_not_analyticAt`).
-/

namespace AlternatingAnalyticChallenge.PropD_9

open AlternatingAnalytic

universe u

/-- The standard operator norm on the space of candidate lifts
`L(A, A)^n → L(Alt^k(A; C), Alt^k(A; C))`, exposed as a local instance because typeclass search
does not find `ContinuousMultilinearMap.hasOpNorm` through the nested alternating-map codomain
on its own. (This mirrors the library's local instance in `BaseChangeLiftDescent.lean`.) -/
noncomputable local instance liftOpNorm {R A C : Type*} [NontriviallyNormedField R]
    [NormedAddCommGroup A] [NormedSpace R A] [NormedAddCommGroup C] [NormedSpace R C]
    {k n : ℕ} :
    Norm (ContinuousMultilinearMap R (fun _ : Fin n => A →L[R] A)
      ((A [⋀^Fin k]→L[R] C) →L[R] (A [⋀^Fin k]→L[R] C))) :=
  ContinuousMultilinearMap.hasOpNorm (𝕜 := R) (E := fun _ : Fin n => A →L[R] A)
    (G := (A [⋀^Fin k]→L[R] C) →L[R] (A [⋀^Fin k]→L[R] C))

/-- Proposition D.9, first sentence: a bounded `k`-linear lift of `A^{k,K'}_{E,E;F}` over `K'`
descends to a bounded `k`-linear lift of `A^{k,K₁}_{E₁,E₁;F₁}` over `K₁` with `‖P₁‖ ≤ ‖P‖`. -/
theorem exists_lift_descent
    (K₁ : Type*) (E₁ F₁ K' : Type u) [NontriviallyNormedField K₁] [CompleteSpace K₁]
    [IsUltrametricDist K₁] [SphericallyCompleteSpace K₁]
    [NontriviallyNormedField K'] [NormedAlgebra K₁ K'] [IsUltrametricDist K']
    [NormedAddCommGroup E₁] [NormedSpace K₁ E₁]
    [NormedAddCommGroup F₁] [NormedSpace K₁ F₁] [CompleteSpace F₁] (k : ℕ)
    (P : ContinuousMultilinearMap K'
      (fun _ : Fin k => CompletedBaseChange K₁ E₁ K' →L[K'] CompletedBaseChange K₁ E₁ K')
      ((CompletedBaseChange K₁ E₁ K' [⋀^Fin k]→L[K'] CompletedBaseChange K₁ F₁ K') →L[K']
        (CompletedBaseChange K₁ E₁ K' [⋀^Fin k]→L[K'] CompletedBaseChange K₁ F₁ K')))
    (hP : ∀ g : CompletedBaseChange K₁ E₁ K' →L[K'] CompletedBaseChange K₁ E₁ K',
      P (fun _ => g) = ContinuousAlternatingMap.compContinuousLinearMapCLM g) :
    ∃ P₁ : ContinuousMultilinearMap K₁ (fun _ : Fin k => E₁ →L[K₁] E₁)
        ((E₁ [⋀^Fin k]→L[K₁] F₁) →L[K₁] (E₁ [⋀^Fin k]→L[K₁] F₁)),
      ‖P₁‖ ≤ ‖P‖ ∧
        ∀ f : E₁ →L[K₁] E₁,
          P₁ (fun _ => f) = ContinuousAlternatingMap.compContinuousLinearMapCLM f :=
  exists_baseChangeLiftDescent K₁ E₁ F₁ K' k P hP

/-- Proposition D.9, second sentence: if `A^{k,K₁}_{E₁,E₁;F₁}` is analytic at no point, then
`A^{k,K'}_{E,E;F}` is analytic at no point. -/
theorem nowhere_analytic_ascends
    (K₁ : Type*) (E₁ F₁ K' : Type u) [NontriviallyNormedField K₁] [CompleteSpace K₁]
    [IsUltrametricDist K₁] [SphericallyCompleteSpace K₁]
    [NontriviallyNormedField K'] [NormedAlgebra K₁ K'] [IsUltrametricDist K']
    [NormedAddCommGroup E₁] [NormedSpace K₁ E₁]
    [NormedAddCommGroup F₁] [NormedSpace K₁ F₁] [CompleteSpace F₁] (k : ℕ)
    (h : ∀ f₀ : E₁ →L[K₁] E₁, ¬ AnalyticAt K₁
      (fun f : E₁ →L[K₁] E₁ =>
        (ContinuousAlternatingMap.compContinuousLinearMapCLM f :
          (E₁ [⋀^Fin k]→L[K₁] F₁) →L[K₁] (E₁ [⋀^Fin k]→L[K₁] F₁))) f₀)
    (g₀ : CompletedBaseChange K₁ E₁ K' →L[K'] CompletedBaseChange K₁ E₁ K') :
    ¬ AnalyticAt K'
      (fun g : CompletedBaseChange K₁ E₁ K' →L[K'] CompletedBaseChange K₁ E₁ K' =>
        (ContinuousAlternatingMap.compContinuousLinearMapCLM g :
          (CompletedBaseChange K₁ E₁ K' [⋀^Fin k]→L[K'] CompletedBaseChange K₁ F₁ K') →L[K']
            (CompletedBaseChange K₁ E₁ K' [⋀^Fin k]→L[K'] CompletedBaseChange K₁ F₁ K'))) g₀ :=
  not_analyticAt_completedBaseChange_of_not_analyticAt K₁ E₁ F₁ K' k (h 0) g₀

end AlternatingAnalyticChallenge.PropD_9
