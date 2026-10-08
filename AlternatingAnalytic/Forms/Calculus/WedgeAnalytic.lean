import AlternatingAnalytic.Forms.Calculus.AmbientBasic

/-!
# The wedge product on multilinear coefficient spaces

The shuffle formula defines a bounded bilinear operation on the multilinear coefficient spaces:
`wedgeMult : Mult^k(P; K) × Mult^l(P; K) → Mult^{k+l}(P; K)` sends `(f, g)` to
`∑_σ sign σ · (f ⊗ g) ∘ σ`, the sum running over one representative of each shuffle class. On
alternating maps it is the wedge product, `j (μ ∧ ν) = wedgeMult (j μ) (j ν)`. Hence the wedge
product of ambient analytic forms is ambient analytic, and its derivative is given by the
product rule.
-/

set_option maxSynthPendingDepth 3

open Filter Set Equiv
open scoped Topology

namespace AlternatingAnalytic.Forms

variable {K : Type*} [NontriviallyNormedField K]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace K P] {k l : ℕ}

variable (K P k l) in
/-- The shuffle product as a continuous bilinear map on multilinear coefficient spaces. -/
noncomputable def wedgeMult :
    ContinuousMultilinearMap K (fun _ : Fin k => P) K →L[K]
      ContinuousMultilinearMap K (fun _ : Fin l => P) K →L[K]
        ContinuousMultilinearMap K (fun _ : Fin (k + l) => P) K :=
  (ContinuousLinearMap.compL K _ _ _
    (∑ q : Perm.ModSumCongr (Fin k) (Fin l), (Perm.sign (Quotient.out q) : ℤ) •
      ((ContinuousMultilinearMap.domDomCongrₗᵢ K P K
          finSumFinEquiv).toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((ContinuousMultilinearMap.domDomCongrₗᵢ K P K
            (Quotient.out q)).toContinuousLinearEquiv.toContinuousLinearMap.comp
          (ContinuousMultilinearMap.currySumEquiv K (Fin k) (Fin l) P
            K).symm.toContinuousLinearEquiv.toContinuousLinearMap)))).comp
    (ContinuousMultilinearMap.smulRightL K (fun _ : Fin k => P)
      (ContinuousMultilinearMap K (fun _ : Fin l => P) K))

/-- The value of `wedgeMult`. -/
theorem wedgeMult_apply (f : ContinuousMultilinearMap K (fun _ : Fin k => P) K)
    (g : ContinuousMultilinearMap K (fun _ : Fin l => P) K) (v : Fin (k + l) → P) :
    wedgeMult K P k l f g v = ∑ q : Perm.ModSumCongr (Fin k) (Fin l),
      (Perm.sign (Quotient.out q) : ℤ) •
        (f (fun i => v (finSumFinEquiv (Quotient.out q (Sum.inl i)))) *
          g (fun j => v (finSumFinEquiv (Quotient.out q (Sum.inr j))))) := by
  simp only [wedgeMult, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.compL_apply, sum_apply, smul_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  rfl

/-- A shuffle summand, computed at the chosen representative of its class. -/
theorem summand_eq_out {μ : P [⋀^Fin k]→ₗ[K] K} {ν : P [⋀^Fin l]→ₗ[K] K}
    (q : Perm.ModSumCongr (Fin k) (Fin l)) :
    AlternatingMap.domCoprod.summand μ ν q =
      Perm.sign (Quotient.out q) • MultilinearMap.domDomCongr (Quotient.out q)
        ((μ : MultilinearMap K (fun _ : Fin k => P) K).domCoprod
          (ν : MultilinearMap K (fun _ : Fin l => P) K)) := by
  conv_lhs => rw [← Quotient.out_eq q]
  rfl

/-- The wedge product, seen in the multilinear coefficient space. -/
theorem toContinuousMultilinearMap_wedge (μ : P [⋀^Fin k]→L[K] K) (ν : P [⋀^Fin l]→L[K] K) :
    (wedge μ ν).toContinuousMultilinearMap =
      wedgeMult K P k l μ.toContinuousMultilinearMap ν.toContinuousMultilinearMap := by
  ext v
  rw [wedgeMult_apply]
  change shuffle μ.toAlternatingMap ν.toAlternatingMap v = _
  simp only [shuffle, AlternatingMap.domDomCongr_apply, LinearMap.compAlternatingMap_apply,
    AlternatingMap.domCoprod_apply, sum_apply, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [summand_eq_out]
  have hu : ∀ (u : ℤˣ) (m : MultilinearMap K (fun _ : Fin k ⊕ Fin l => P) (TensorProduct K K K))
      (x : Fin k ⊕ Fin l → P), (u • m) x = u • m x := fun _ _ _ => rfl
  rw [hu, map_zsmul_unit]
  simp only [MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply,
    LinearMap.mul'_apply, Function.comp_apply, Units.smul_def, zsmul_eq_mul]
  rfl

/-- The wedge product of ambient analytic forms is ambient analytic. -/
theorem IsAmbientAnalyticOn.wedge {U : Set P} {η : P → P [⋀^Fin k]→L[K] K}
    {ζ : P → P [⋀^Fin l]→L[K] K} (hη : IsAmbientAnalyticOn η U)
    (hζ : IsAmbientAnalyticOn ζ U) :
    IsAmbientAnalyticOn (fun y => Forms.wedge (η y) (ζ y)) U := by
  intro y hy
  have h := AnalyticAt.comp
    (f := fun x => ((η x).toContinuousMultilinearMap, (ζ x).toContinuousMultilinearMap)) (x := y)
    (ContinuousLinearMap.analyticAt_bilinear (wedgeMult K P k l) _) ((hη y hy).prod (hζ y hy))
  refine h.congr (Eventually.of_forall fun x => ?_)
  exact (toContinuousMultilinearMap_wedge (η x) (ζ x)).symm

/-- Product rule for the wedge product of ambient analytic forms. -/
theorem fderiv_wedge_apply {η : P → P [⋀^Fin k]→L[K] K} {ζ : P → P [⋀^Fin l]→L[K] K} {y : P}
    (hη : AnalyticAt K (fun x => (η x).toContinuousMultilinearMap) y)
    (hζ : AnalyticAt K (fun x => (ζ x).toContinuousMultilinearMap) y) (w : P) :
    fderiv K (fun x => Forms.wedge (η x) (ζ x)) y w =
      Forms.wedge (fderiv K η y w) (ζ y) + Forms.wedge (η y) (fderiv K ζ y w) := by
  have hB := (wedgeMult K P k l).hasFDerivAt_of_bilinear hη.differentiableAt.hasFDerivAt
    hζ.differentiableAt.hasFDerivAt
  have hfun : (fun x => wedgeMult K P k l (η x).toContinuousMultilinearMap
      (ζ x).toContinuousMultilinearMap) =
      fun x => (Forms.wedge (η x) (ζ x)).toContinuousMultilinearMap :=
    funext fun x => (toContinuousMultilinearMap_wedge (η x) (ζ x)).symm
  rw [hfun] at hB
  have hA : AnalyticAt K (fun x => (Forms.wedge (η x) (ζ x)).toContinuousMultilinearMap) y := by
    have h := AnalyticAt.comp
      (f := fun x => ((η x).toContinuousMultilinearMap, (ζ x).toContinuousMultilinearMap))
      (x := y) (ContinuousLinearMap.analyticAt_bilinear (wedgeMult K P k l) _) (hη.prod hζ)
    refine h.congr (Eventually.of_forall fun x => ?_)
    exact (toContinuousMultilinearMap_wedge (η x) (ζ x)).symm
  obtain ⟨M, hM, hJ⟩ := exists_hasFDerivAt_of_analyticAt hA
  rw [hM.fderiv]
  apply (inclLI K P K (k + l)).injective
  have h1 := DFunLike.congr_fun hJ w
  rw [hB.fderiv] at h1
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    LinearIsometry.coe_toContinuousLinearMap] at h1
  rw [h1]
  simp only [add_apply, ContinuousLinearMap.precompR_apply, ContinuousLinearMap.precompL_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.coe_comp, Function.comp_apply]
  rw [← toContinuousMultilinearMap_fderiv_apply hη, ← toContinuousMultilinearMap_fderiv_apply hζ]
  simp only [map_add, ContinuousAlternatingMap.toContinuousMultilinearMapLI_apply,
    toContinuousMultilinearMap_wedge]
  exact add_comm _ _

end AlternatingAnalytic.Forms
