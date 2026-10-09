import AlternatingAnalytic.Analysis.CompletedBaseChange
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Analytic.Basic

/-!
# Proposition D.9 (descent of a lift), p. 48

Paper statement (Appendix D). "Assume (H1) and (H2). Let `E₁` be a normed `K₁`-space, `F₁` a
`K₁`-Banach space, and `E, F` as above [`E = E₁ ⊗̂_π K'`, `F = F₁ ⊗̂_π K'`]. If `A^{k,K'}_{E,E;F}`
admits a bounded `k`-linear lift `P` over `K'`, then `A^{k,K₁}_{E₁,E₁;F₁}` admits a bounded
`k`-linear lift `P₁` over `K₁` with `‖P₁‖ ≤ ‖P‖`. Equivalently, by Proposition 3.3 over `K₁`
and over `K'`: if `A^{k,K₁}_{E₁,E₁;F₁}` is analytic at no point, then `A^{k,K'}_{E,E;F}` is
analytic at no point either."  Here (H1): `K₁` with the restricted absolute value is
nontrivially normed, complete and spherically complete; (H2): `K' ⊇ K₁` is nonarchimedean.
`A^k_{E,E;F}(f) = (m ↦ m ∘ (f, …, f))`.

## Formalization notes

* `A^k` is `ContinuousAlternatingMap.compContinuousLinearMapCLM`, indexed by `Fin k`.
* A bounded `k`-linear lift is a continuous multilinear map
  `P : L(E,E)^k → L(Alt^k(E;F), Alt^k(E;F))` with `P (g, …, g) = A^k(g)`. `‖P‖` is the
  multilinear operator norm, supplied by the local instance `liftOpNorm`.
* `E = CompletedBaseChange K₁ E₁ K'` and `F = CompletedBaseChange K₁ F₁ K'` are library
  definitions from `AlternatingAnalytic/Analysis/CompletedBaseChange.lean`.
* `K₁ ⊆ K'` is `[NormedAlgebra K₁ K']`; (H1) is `[CompleteSpace K₁] [SphericallyCompleteSpace K₁]`;
  (H2) is `[IsUltrametricDist K']`. The library also needs `[IsUltrametricDist K₁]`, which
  follows from (H2). `E₁`, `F₁`, `K'` lie in one universe.
* `K'` is a `NontriviallyNormedField`; this follows from containing `K₁` isometrically.
* The "equivalently" sentence is a separate theorem, `nowhere_analytic_ascends`.
-/

namespace AlternatingAnalyticChallenge.PropD_9

open AlternatingAnalytic

universe u

/-- The operator norm on candidate lifts. Instance search does not find
`ContinuousMultilinearMap.hasOpNorm` through the alternating-map codomain. -/
noncomputable local instance liftOpNorm {R A C : Type*} [NontriviallyNormedField R]
    [NormedAddCommGroup A] [NormedSpace R A] [NormedAddCommGroup C] [NormedSpace R C]
    {k n : ℕ} :
    Norm (ContinuousMultilinearMap R (fun _ : Fin n => A →L[R] A)
      ((A [⋀^Fin k]→L[R] C) →L[R] (A [⋀^Fin k]→L[R] C))) :=
  ContinuousMultilinearMap.hasOpNorm (𝕜 := R) (E := fun _ : Fin n => A →L[R] A)
    (G := (A [⋀^Fin k]→L[R] C) →L[R] (A [⋀^Fin k]→L[R] C))

/-- A bounded `k`-linear lift of `A^{k,K'}_{E,E;F}` over `K'` gives a bounded `k`-linear lift of
`A^{k,K₁}_{E₁,E₁;F₁}` over `K₁` with `‖P₁‖ ≤ ‖P‖`. -/
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
          P₁ (fun _ => f) = ContinuousAlternatingMap.compContinuousLinearMapCLM f := by
  sorry

/-- If `A^{k,K₁}_{E₁,E₁;F₁}` is analytic at no point, then neither is `A^{k,K'}_{E,E;F}`. -/
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
            (CompletedBaseChange K₁ E₁ K' [⋀^Fin k]→L[K'] CompletedBaseChange K₁ F₁ K'))) g₀ := by
  sorry

end AlternatingAnalyticChallenge.PropD_9
