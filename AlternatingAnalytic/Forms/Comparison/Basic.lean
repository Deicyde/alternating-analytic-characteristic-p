import AlternatingAnalytic.Geometry.AnalyticAlternatingBundle
import AlternatingAnalytic.Analysis.AlternatingActionRegularity
import AlternatingAnalytic.Analysis.FiniteCoordinateFamilies
import AlternatingAnalytic.Analysis.FiniteCoordinateReflection

/-!
# Intrinsic and ambient analytic forms

This file proves the comparison of `paper/charp.tex`, Proposition 7.3. A coefficient map
`η : P → Alt^k(P; F)` is ambient analytic when `j ∘ η` is analytic, where
`j : Alt^k(P; F) → Mult^k(P; F)` forgets alternation. Intrinsic analyticity implies ambient
analyticity. If `j` has a bounded linear retraction, or if `P` has finitely many continuous
coordinates, the converse holds, the alternating transitions `y ↦ (Dψ(y))^*` of `C^ω` maps are
analytic, and (for a retraction) the alternating bundle over a `C^n` manifold is `C^n`. No
completeness of the field and no ultrametric hypothesis is needed.
-/

noncomputable section

open Set
open scoped ContDiff Manifold

namespace AlternatingAnalytic

variable {K : Type*} [NontriviallyNormedField K]
  {P F : Type*} [NormedAddCommGroup P] [NormedSpace K P]
  [NormedAddCommGroup F] [NormedSpace K F]

section Retraction

variable {ι : Type*} [Fintype ι] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace K E']

/-- A continuous linear retraction of `j` makes precomposition `C^n`, for any target. -/
theorem contDiff_compContinuousLinearMapCLM_of_retraction' {n : WithTop ℕ∞}
    (r : ContinuousMultilinearMap K (fun _ : ι => P) F →L[K] (P [⋀^ι]→L[K] F))
    (hr : ∀ a : P [⋀^ι]→L[K] F, r a.toContinuousMultilinearMap = a) :
    ContDiff K n (ContinuousAlternatingMap.compContinuousLinearMapCLM :
      (P →L[K] E') → (E' [⋀^ι]→L[K] F) →L[K] (P [⋀^ι]→L[K] F)) := by
  have hamb : ContDiff K n fun f : P →L[K] E' ↦
      (ContinuousMultilinearMap.compContinuousLinearMapL (F := F) fun _ : ι ↦ f).comp
        (ContinuousAlternatingMap.toContinuousMultilinearMapCLM K) :=
    ((ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear K
      (fun _ : ι ↦ P) (fun _ ↦ E') F).contDiff.comp
      (contDiff_pi.2 fun _ ↦ contDiff_id)).clm_comp contDiff_const
  have := (contDiff_const (c := r) (𝕜 := K) (n := n) (E := P →L[K] E')).clm_comp hamb
  convert this using 2 with f
  refine ContinuousLinearMap.ext fun m => ?_
  exact (hr (m.compContinuousLinearMap f)).symm

end Retraction

variable {k : ℕ}

/-- Intrinsically analytic coefficient maps are ambient analytic. -/
theorem analyticOnNhd_toContinuousMultilinearMap {U : Set P} {η : P → P [⋀^Fin k]→L[K] F}
    (hη : AnalyticOnNhd K η U) :
    AnalyticOnNhd K (fun y => (η y).toContinuousMultilinearMap) U := fun x hx =>
  ((ContinuousAlternatingMap.toContinuousMultilinearMapCLM (𝕜 := K) (E := P) (F := F)
    (ι := Fin k) K).analyticAt (η x)).comp (hη x hx)

/-- With a bounded linear retraction of `j`, ambient analyticity is intrinsic analyticity. -/
theorem analyticOnNhd_iff_toContinuousMultilinearMap_of_retraction
    (R : ContinuousMultilinearMap K (fun _ : Fin k => P) F →L[K] (P [⋀^Fin k]→L[K] F))
    (hR : ∀ a : P [⋀^Fin k]→L[K] F, R a.toContinuousMultilinearMap = a)
    (U : Set P) (η : P → P [⋀^Fin k]→L[K] F) :
    AnalyticOnNhd K η U ↔ AnalyticOnNhd K (fun y => (η y).toContinuousMultilinearMap) U := by
  refine ⟨analyticOnNhd_toContinuousMultilinearMap, fun h x hx => ?_⟩
  have heq : η = fun y => R (η y).toContinuousMultilinearMap := funext fun y => (hR _).symm
  rw [heq]
  exact (R.analyticAt _).comp (h x hx)

/-- With finite continuous coordinates on `P`, ambient analyticity is intrinsic analyticity. -/
theorem analyticOnNhd_iff_toContinuousMultilinearMap_of_finiteCoordinates {d : ℕ}
    (c : P ≃L[K] (Fin d → K)) (U : Set P) (η : P → P [⋀^Fin k]→L[K] F) :
    AnalyticOnNhd K η U ↔ AnalyticOnNhd K (fun y => (η y).toContinuousMultilinearMap) U :=
  ⟨analyticOnNhd_toContinuousMultilinearMap, fun h x hx =>
    analyticAt_of_closed_linearIsometry_of_equiv c
      (ContinuousAlternatingMap.toContinuousMultilinearMapLI (𝕜 := K) (E := P) (F := F)
        (ι := Fin k))
      ContinuousAlternatingMap.isClosed_range_toContinuousMultilinearMap (h x hx)⟩

/-- The derivative of a `C^ω` map on an open set is analytic there. -/
theorem analyticOnNhd_fderiv_of_contDiffOn {U : Set P} {ψ : P → P} (hU : IsOpen U)
    (hψ : ContDiffOn K ω ψ U) : AnalyticOnNhd K (fderiv K ψ) U :=
  hU.analyticOn_iff_analyticOnNhd.mp (hψ.fderiv_of_isOpen hU le_top).analyticOn

/-- With a bounded linear retraction of `j`, the alternating transitions of a `C^ω` map are
analytic. -/
theorem analyticOnNhd_compContinuousLinearMapCLM_fderiv_of_retraction
    (R : ContinuousMultilinearMap K (fun _ : Fin k => P) F →L[K] (P [⋀^Fin k]→L[K] F))
    (hR : ∀ a : P [⋀^Fin k]→L[K] F, R a.toContinuousMultilinearMap = a)
    {U : Set P} {ψ : P → P} (hU : IsOpen U) (hψ : ContDiffOn K ω ψ U) :
    AnalyticOnNhd K
      (fun y => (ContinuousAlternatingMap.compContinuousLinearMapCLM (fderiv K ψ y) :
        (P [⋀^Fin k]→L[K] F) →L[K] (P [⋀^Fin k]→L[K] F))) U := fun y hy =>
  (((contDiff_compContinuousLinearMapCLM_of_retraction' (E' := P) (n := ω) R hR).analyticOnNhd
    (s := univ)) _ trivial).comp (analyticOnNhd_fderiv_of_contDiffOn hU hψ y hy)

/-- With finite continuous coordinates on `P`, the alternating transitions of a `C^ω` map are
analytic. -/
theorem analyticOnNhd_compContinuousLinearMapCLM_fderiv_of_finiteCoordinates {d : ℕ}
    (c : P ≃L[K] (Fin d → K)) {U : Set P} {ψ : P → P} (hU : IsOpen U)
    (hψ : ContDiffOn K ω ψ U) :
    AnalyticOnNhd K
      (fun y => (ContinuousAlternatingMap.compContinuousLinearMapCLM (fderiv K ψ y) :
        (P [⋀^Fin k]→L[K] F) →L[K] (P [⋀^Fin k]→L[K] F))) U := by
  intro y hy
  have h := analyticAt_alternatingMapAction_comp_of_finite_coordinates (E := P) (F := F)
    (F' := F) c k (γ := fun y => (fderiv K ψ y, ContinuousLinearMap.id K F))
    ((analyticOnNhd_fderiv_of_contDiffOn hU hψ y hy).prod analyticAt_const)
  have heq : (alternatingMapAction k ∘ fun y => (fderiv K ψ y, ContinuousLinearMap.id K F)) =
      fun y => (ContinuousAlternatingMap.compContinuousLinearMapCLM (fderiv K ψ y) :
        (P [⋀^Fin k]→L[K] F) →L[K] (P [⋀^Fin k]→L[K] F)) :=
    funext fun y => alternatingMapAction_id_right k (fderiv K ψ y)
  rwa [heq] at h

end AlternatingAnalytic
