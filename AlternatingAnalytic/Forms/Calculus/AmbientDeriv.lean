import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Calculus.ContDiff.LinearIsometry
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import AlternatingAnalytic.Forms.Calculus.Defs

/-!
# Derivatives of ambient analytic forms

Let `η : P → Alt^k(P; F)` be ambient analytic on an open set `U`. The inclusion
`j : Alt^k(P; F) → Mult^k(P; F)` is a linear isometry with closed range, so the first and second
derivatives of `j ∘ η` factor through `j` (`LinearIsometry.exists_hasFDerivAt_of_comp`). Hence the
second derivative of `η` is symmetric, `d(dη) = 0`, and `dη` is ambient analytic, as in the proof
of Theorem 7.2.
-/

set_option maxSynthPendingDepth 3

open Filter Set
open scoped Topology ContDiff

namespace AlternatingAnalytic.Forms

variable {K : Type*} [NontriviallyNormedField K]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace K P]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace K F] {k : ℕ}

/-- The inclusion `j : Alt^k(P; F) → Mult^k(P; F)` as a linear isometry. -/
noncomputable abbrev inclLI (K P F : Type*) [NontriviallyNormedField K] [NormedAddCommGroup P]
    [NormedSpace K P] [NormedAddCommGroup F] [NormedSpace K F] (k : ℕ) :
    (P [⋀^Fin k]→L[K] F) →ₗᵢ[K] ContinuousMultilinearMap K (fun _ : Fin k => P) F :=
  ContinuousAlternatingMap.toContinuousMultilinearMapLI

/-- The inclusion `j` has closed range. -/
theorem isClosed_range_inclLI : IsClosed (range (inclLI K P F k)) :=
  ContinuousAlternatingMap.isClosed_range_toContinuousMultilinearMap

/-- The multilinear version of `alternatizeUncurryFin`:
`B ↦ (v ↦ ∑ᵢ (-1)^i B(vᵢ)(v₀, …, v̂ᵢ, …, v_k))`. -/
noncomputable def multAlternatizeUncurryFin (K P F : Type*) [NontriviallyNormedField K]
    [NormedAddCommGroup P] [NormedSpace K P] [NormedAddCommGroup F] [NormedSpace K F] (k : ℕ) :
    (P →L[K] ContinuousMultilinearMap K (fun _ : Fin k => P) F) →L[K]
      ContinuousMultilinearMap K (fun _ : Fin (k + 1) => P) F :=
  ∑ i : Fin (k + 1), ((-1 : K) ^ (i : ℕ)) •
    ((ContinuousMultilinearMap.domDomCongrₗᵢ K P F
        (Fin.cycleRange i).symm).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (continuousMultilinearCurryLeftEquiv K (fun _ : Fin (k + 1) => P)
        F).symm.toContinuousLinearEquiv.toContinuousLinearMap)

/-- The value of `multAlternatizeUncurryFin`. -/
theorem multAlternatizeUncurryFin_apply
    (B : P →L[K] ContinuousMultilinearMap K (fun _ : Fin k => P) F) (v : Fin (k + 1) → P) :
    multAlternatizeUncurryFin K P F k B v =
      ∑ i : Fin (k + 1), (-1 : K) ^ (i : ℕ) • B (v i) (Fin.removeNth i v) := by
  simp only [multAlternatizeUncurryFin, ContinuousLinearMap.coe_comp, Function.comp_apply,
    sum_apply, smul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  change ((continuousMultilinearCurryLeftEquiv K (fun _ : Fin (k + 1) => P) F).symm B)
    (fun j => v ((Fin.cycleRange i).symm j)) = _
  rw [continuousMultilinearCurryLeftEquiv_symm_apply, Fin.cycleRange_symm_zero]
  congr 1
  funext j
  simp [Fin.tail, Fin.removeNth, Fin.cycleRange_symm_succ]

/-- `multAlternatizeUncurryFin` extends `alternatizeUncurryFin` along `j`. -/
theorem multAlternatizeUncurryFin_comp (A : P →L[K] P [⋀^Fin k]→L[K] F) :
    multAlternatizeUncurryFin K P F k ((inclLI K P F k).toContinuousLinearMap.comp A) =
      inclLI K P F (k + 1) (ContinuousAlternatingMap.alternatizeUncurryFin A) := by
  ext v
  rw [multAlternatizeUncurryFin_apply]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap,
    ContinuousAlternatingMap.toContinuousMultilinearMapLI_apply,
    ContinuousAlternatingMap.coe_toContinuousMultilinearMap,
    ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Int.cast_smul_eq_zsmul K, Int.cast_pow, Int.cast_neg, Int.cast_one]

/-- The derivative of `j ∘ η` factors through `j`, and the factor is a derivative of `η`. -/
theorem exists_hasFDerivAt_of_analyticAt {η : P → P [⋀^Fin k]→L[K] F} {y : P}
    (h : AnalyticAt K (fun x => (η x).toContinuousMultilinearMap) y) :
    ∃ M : P →L[K] P [⋀^Fin k]→L[K] F, HasFDerivAt η M y ∧
      (inclLI K P F k).toContinuousLinearMap.comp M =
        fderiv K (fun x => (η x).toContinuousMultilinearMap) y :=
  (inclLI K P F k).exists_hasFDerivAt_of_comp isClosed_range_inclLI h.differentiableAt.hasFDerivAt

/-- An ambient analytic form is differentiable as an `Alt`-valued map. -/
theorem differentiableAt_of_analyticAt {η : P → P [⋀^Fin k]→L[K] F} {y : P}
    (h : AnalyticAt K (fun x => (η x).toContinuousMultilinearMap) y) :
    DifferentiableAt K η y :=
  (exists_hasFDerivAt_of_analyticAt h).choose_spec.1.differentiableAt

/-- The derivative of an ambient analytic form, followed by `j`, is the derivative of `j ∘ η`. -/
theorem inclLI_comp_fderiv {η : P → P [⋀^Fin k]→L[K] F} {y : P}
    (h : AnalyticAt K (fun x => (η x).toContinuousMultilinearMap) y) :
    (inclLI K P F k).toContinuousLinearMap.comp (fderiv K η y) =
      fderiv K (fun x => (η x).toContinuousMultilinearMap) y := by
  obtain ⟨M, hM, hJ⟩ := exists_hasFDerivAt_of_analyticAt h
  rw [hM.fderiv, hJ]

variable [CompleteSpace F]

omit [CompleteSpace F] in
/-- Pointwise form of `inclLI_comp_fderiv`. -/
theorem toContinuousMultilinearMap_fderiv_apply {η : P → P [⋀^Fin k]→L[K] F} {y : P}
    (h : AnalyticAt K (fun x => (η x).toContinuousMultilinearMap) y) (w : P) :
    (fderiv K η y w).toContinuousMultilinearMap =
      fderiv K (fun x => (η x).toContinuousMultilinearMap) y w := by
  rw [← inclLI_comp_fderiv h]
  rfl

/-- The derivative of an ambient analytic form is differentiable, and its derivative factors
through `j`. -/
theorem exists_hasFDerivAt_fderiv {η : P → P [⋀^Fin k]→L[K] F} {U : Set P} (hU : IsOpen U)
    (hη : AnalyticOnNhd K (fun x => (η x).toContinuousMultilinearMap) U) {y : P} (hy : y ∈ U) :
    ∃ M : P →L[K] P →L[K] P [⋀^Fin k]→L[K] F, HasFDerivAt (fderiv K η) M y ∧
      (LinearIsometry.postcomp (E := P) (σ₁₂ := RingHom.id K)
        (inclLI K P F k)).toContinuousLinearMap.comp M =
        fderiv K (fderiv K (fun x => (η x).toContinuousMultilinearMap)) y := by
  set Φ := LinearIsometry.postcomp (E := P) (σ₁₂ := RingHom.id K) (inclLI K P F k)
  have hd : HasFDerivAt (fderiv K (fun x => (η x).toContinuousMultilinearMap))
      (fderiv K (fderiv K (fun x => (η x).toContinuousMultilinearMap)) y) y :=
    ((hη.fderiv y hy).differentiableAt).hasFDerivAt
  have heq : (fun x => Φ (fderiv K η x)) =ᶠ[𝓝 y]
      fderiv K (fun x => (η x).toContinuousMultilinearMap) := by
    filter_upwards [hU.mem_nhds hy] with x hx
    exact inclLI_comp_fderiv (hη x hx)
  have hcl : IsClosed (range Φ) :=
    (inclLI K P F k).isClosed_range_postcomp isClosed_range_inclLI
  exact Φ.exists_hasFDerivAt_of_comp hcl (hd.congr_of_eventuallyEq heq)

/-- The second derivative of an ambient analytic form is symmetric. -/
theorem isSymmSndFDerivAt_of_isAmbientAnalyticOn {η : P → P [⋀^Fin k]→L[K] F} {U : Set P}
    (hU : IsOpen U) (hη : AnalyticOnNhd K (fun x => (η x).toContinuousMultilinearMap) U) {y : P}
    (hy : y ∈ U) :
    IsSymmSndFDerivAt K η y := by
  intro v w
  obtain ⟨M, hM, hJ⟩ := exists_hasFDerivAt_fderiv hU hη hy
  have hsymm := ((hη y hy).contDiffAt (n := ω)).isSymmSndFDerivAt_of_omega v w
  rw [hM.fderiv]
  apply (inclLI K P F k).injective
  have h1 := congrArg (fun L => L v w) hJ
  have h2 := congrArg (fun L => L w v) hJ
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.postcomp_apply] at h1 h2
  rw [h1, h2]
  exact hsymm

/-- `d² = 0` for ambient analytic forms. -/
theorem extDeriv_extDeriv_apply {η : P → P [⋀^Fin k]→L[K] F} {U : Set P} (hU : IsOpen U)
    (hη : AnalyticOnNhd K (fun x => (η x).toContinuousMultilinearMap) U) {y : P} (hy : y ∈ U) :
    _root_.extDeriv (_root_.extDeriv η) y = 0 := by
  obtain ⟨M, hM, -⟩ := exists_hasFDerivAt_fderiv hU hη hy
  have hcomp :=
    (ContinuousAlternatingMap.alternatizeUncurryFinCLM K P F (n := k)).hasFDerivAt.comp y hM
  have hfun : _root_.extDeriv η =
      ⇑(ContinuousAlternatingMap.alternatizeUncurryFinCLM K P F (n := k)) ∘
      fderiv K η := rfl
  have hsymm : ∀ v w, M v w = M w v := fun v w => by
    have := isSymmSndFDerivAt_of_isAmbientAnalyticOn hU hη hy v w
    rwa [hM.fderiv] at this
  change ContinuousAlternatingMap.alternatizeUncurryFin (fderiv K (_root_.extDeriv η) y) = 0
  rw [hfun, hcomp.fderiv]
  exact ContinuousAlternatingMap.alternatizeUncurryFin_alternatizeUncurryFinCLM_comp_of_symmetric
    hsymm

/-- The exterior derivative of an ambient analytic form is ambient analytic. -/
theorem isAmbientAnalyticOn_extDeriv {η : P → P [⋀^Fin k]→L[K] F} {U : Set P} (hU : IsOpen U)
    (hη : AnalyticOnNhd K (fun x => (η x).toContinuousMultilinearMap) U) :
    AnalyticOnNhd K (fun x => (_root_.extDeriv η x).toContinuousMultilinearMap) U := by
  intro y hy
  have h1 := ((multAlternatizeUncurryFin K P F k).analyticAt _).comp (hη.fderiv y hy)
  refine h1.congr ?_
  filter_upwards [hU.mem_nhds hy] with x hx
  simp only [Function.comp_apply]
  rw [← inclLI_comp_fderiv (hη x hx), multAlternatizeUncurryFin_comp]
  rfl

end AlternatingAnalytic.Forms
