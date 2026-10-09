import AlternatingAnalytic.Analysis.CompletedBaseChange
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Analytic.Basic

/-!
# Proposition D.9 (descent of a lift), p. 46

Paper statement (Appendix D). "Assume (H1) and (H2). Let `E₁` be a normed `K₁`-space, `F₁` a
`K₁`-Banach space, and `E, F` as above [`E = E₁ ⊗̂_π K'`, `F = F₁ ⊗̂_π K'`]. If `A^{k,K'}_{E,E;F}`
admits a bounded `k`-linear lift `P` over `K'`, then `A^{k,K₁}_{E₁,E₁;F₁}` admits a bounded
`k`-linear lift `P₁` over `K₁` with `‖P₁‖ ≤ ‖P‖`. Equivalently, by Proposition 3.3 over `K₁`
and over `K'`: if `A^{k,K₁}_{E₁,E₁;F₁}` is analytic at no point, then `A^{k,K'}_{E,E;F}` is
analytic at no point either."  Here (H1): `K₁` with the restricted absolute value is
nontrivially normed, complete and spherically complete; (H2): `K' ⊇ K₁` is nonarchimedean.
`A^k_{E,E;F}(f) = (m ↦ m ∘ (f, …, f))`.

## Formalization notes

* `A^k` is `ContinuousAlternatingMap.compContinuousLinearMapCLM`, with degree index `Fin k`.
* A bounded `k`-linear lift of `A^k` is a continuous `k`-multilinear map
  `P : L(E,E)^k → L(Alt^k(E;F), Alt^k(E;F))` with `P (g, …, g) = A^k(g)` for every `g`, written
  out explicitly (the library predicate `Round24Transfer.HasBoundedLift` is not imported).
  `‖P‖` is the usual multilinear operator norm, supplied by the local instance `liftOpNorm`
  (definition `ContinuousMultilinearMap.hasOpNorm`; needed only because instance search does not
  find it unaided).
* The completed projective base changes `E = CompletedBaseChange K₁ E₁ K'`,
  `F = CompletedBaseChange K₁ F₁ K'` are the library's construction, imported as definitions from
  `AlternatingAnalytic.Analysis.CompletedBaseChange`; the proving module
  `BaseChangeLiftDescent.lean` is not imported.
* `K₁ ⊆ K'` isometrically is `[NormedAlgebra K₁ K']`; (H1) is `[CompleteSpace K₁]
  [SphericallyCompleteSpace K₁]`; (H2) is `[IsUltrametricDist K']`. `[IsUltrametricDist K₁]`
  (implied by (H2)) is required by the construction. `E₁`, `F₁`, `K'` share the universe `u`.
* `K'` is taken `NontriviallyNormedField` (automatic: it contains the nontrivially normed `K₁`
  isometrically).
* The "equivalently" sentence is stated as its own theorem: nowhere-analyticity of `A^{k,K₁}`
  implies nowhere-analyticity of `A^{k,K'}`.
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
          P₁ (fun _ => f) = ContinuousAlternatingMap.compContinuousLinearMapCLM f := by
  sorry

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
            (CompletedBaseChange K₁ E₁ K' [⋀^Fin k]→L[K'] CompletedBaseChange K₁ F₁ K'))) g₀ := by
  sorry

end AlternatingAnalyticChallenge.PropD_9
