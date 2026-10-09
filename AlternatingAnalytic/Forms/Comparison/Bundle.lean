import AlternatingAnalytic.Forms.Comparison.Basic

/-!
# Alternating bundles from a bounded retraction

If the inclusion `j : Alt^k(F₁; F₂) → Mult^k(F₁; F₂)` has a bounded linear retraction, the
joint alternating-map action is analytic, so the alternating bundle `x ↦ Alt^k(E₁ x; E₂ x)` of
two `C^n` vector bundles is `C^n`. This is the atlas statement of Proposition 7.3 for manifolds.
-/

noncomputable section

open Bundle Set
open scoped Bundle Manifold ContDiff

namespace AlternatingAnalytic

variable {K : Type*} [NontriviallyNormedField K]
  {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedSpace K F₁]
  [NormedAddCommGroup F₂] [NormedSpace K F₂]

/-- With a bounded retraction of `j`, the joint alternating-map action is `C^n`. -/
theorem contDiff_alternatingMapAction_of_retraction {k : ℕ} {n : WithTop ℕ∞}
    (R : ContinuousMultilinearMap K (fun _ : Fin k => F₁) F₂ →L[K] (F₁ [⋀^Fin k]→L[K] F₂))
    (hR : ∀ a : F₁ [⋀^Fin k]→L[K] F₂, R a.toContinuousMultilinearMap = a) :
    ContDiff K n (alternatingMapAction (K := K) (E := F₁) (E' := F₁) (F := F₂) (F' := F₂) k) := by
  have hQ := contDiff_compContinuousLinearMapCLM_of_retraction' (E' := F₁) (n := ω) R hR
  refine AnalyticOnNhd.contDiff fun z _ => ?_
  exact analyticAt_alternatingMapAction_of_precomposition k z
    (hQ.analyticOnNhd (s := univ) _ trivial)

variable {M : Type*} [TopologicalSpace M]
  {E₁ E₂ : M → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module K (E₁ x)]
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module K (E₂ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [∀ x, TopologicalSpace (E₁ x)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₁ E₁] [VectorBundle K F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle K F₂ E₂]
  [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul K (E₂ x)]
  {P H : Type*} [NormedAddCommGroup P] [NormedSpace K P]
  [TopologicalSpace H] [ChartedSpace H M] {I : ModelWithCorners K P H} {n : WithTop ℕ∞}
  [ContMDiffVectorBundle n F₁ E₁ I] [ContMDiffVectorBundle n F₂ E₂ I]

/-- With a bounded retraction of `j` on the model fibers, the alternating bundle is `C^n`. -/
theorem contMDiffVectorBundle_alternating_of_retraction (k : ℕ)
    (R : ContinuousMultilinearMap K (fun _ : Fin k => F₁) F₂ →L[K] (F₁ [⋀^Fin k]→L[K] F₂))
    (hR : ∀ a : F₁ [⋀^Fin k]→L[K] F₂, R a.toContinuousMultilinearMap = a) :
    ContMDiffVectorBundle n (F₁ [⋀^Fin k]→L[K] F₂)
      (fun x ↦ E₁ x [⋀^Fin k]→L[K] E₂ x) I :=
  contMDiffVectorBundle_alternating_of_family k fun {_} _ {_} hγ =>
    fun x hx => (contDiff_alternatingMapAction_of_retraction (n := n) R hR).comp_contMDiffWithinAt
      (hγ x hx)

end AlternatingAnalytic
