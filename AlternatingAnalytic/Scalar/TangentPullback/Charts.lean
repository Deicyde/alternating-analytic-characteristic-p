import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Add
import AlternatingAnalytic.Scalar.TangentPullback.Compression

/-!
# Two global charts with nonanalytic transition on forms

This is Proposition 6.5(1). On `X = L(E, D) × D × E` the chart change
`ψ(u, d, e) = (u, d + u e, e)` and its inverse `(u, d, e) ↦ (u, d - u e, e)` are polynomial.
Its derivative is `Dψ(u, d, e)(v, a, b) = (v, a + v e + u b, b)`, so the projection to `D`
of `Dψ(u, d, e)` restricted to the `E`-directions is `u`. Compressing the induced transition
on alternating forms along the affine slice `u ↦ (u, d₀, e₀)` recovers the operator
obstruction `A(u) = u^*`; hence the transition is analytic at no point when `A` is analytic
at no point. The same holds for the inverse chart change, using the slice `u ↦ (-u, d₀, e₀)`.
-/

noncomputable section

set_option maxSynthPendingDepth 2

namespace AlternatingAnalytic.TangentPullback

variable {K : Type*} [NontriviallyNormedField K]
  {D E F : Type*}
  [NormedAddCommGroup D] [NormedSpace K D]
  [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup F] [NormedSpace K F]
  {ι : Type*} [Fintype ι]

variable (K D E) in
/-- The model space `L(E, D) × D × E` of the tangent obstruction. -/
abbrev ChartSpace := (E →L[K] D) × D × E

variable (K D E) in
/-- The chart change `(u, d, e) ↦ (u, d + u e, e)`, with inverse `(u, d, e) ↦ (u, d - u e, e)`. -/
def chartShear : ChartSpace K D E ≃ ChartSpace K D E where
  toFun x := (x.1, x.2.1 + x.1 x.2.2, x.2.2)
  invFun x := (x.1, x.2.1 - x.1 x.2.2, x.2.2)
  left_inv x := by simp
  right_inv x := by simp

@[simp]
theorem chartShear_apply (x : ChartSpace K D E) :
    chartShear K D E x = (x.1, x.2.1 + x.1 x.2.2, x.2.2) := rfl

@[simp]
theorem chartShear_symm_apply (x : ChartSpace K D E) :
    (chartShear K D E).symm x = (x.1, x.2.1 - x.1 x.2.2, x.2.2) := rfl

variable (K D E) in
/-- The projection `L(E, D) × D × E → D`. -/
def chartProjD : ChartSpace K D E →L[K] D :=
  (ContinuousLinearMap.fst K D E).comp (ContinuousLinearMap.snd K (E →L[K] D) (D × E))

variable (K D E) in
/-- The inclusion `E → L(E, D) × D × E`, `b ↦ (0, 0, b)`. -/
def chartInclE : E →L[K] ChartSpace K D E :=
  (ContinuousLinearMap.inr K (E →L[K] D) (D × E)).comp (ContinuousLinearMap.inr K D E)

@[simp]
theorem chartProjD_apply (x : ChartSpace K D E) : chartProjD K D E x = x.2.1 := rfl

@[simp]
theorem chartInclE_apply (b : E) : chartInclE K D E b = (0, 0, b) := rfl

/-- The evaluation map `(u, d, e) ↦ u e` has derivative `(v, a, b) ↦ u b + v e`. -/
theorem hasFDerivAt_chartEval (x : ChartSpace K D E) :
    HasFDerivAt (fun y : ChartSpace K D E => y.1 y.2.2)
      ((x.1).comp ((ContinuousLinearMap.snd K D E).comp
          (ContinuousLinearMap.snd K (E →L[K] D) (D × E))) +
        (ContinuousLinearMap.fst K (E →L[K] D) (D × E)).flip x.2.2) x :=
  hasFDerivAt_fst.clm_apply hasFDerivAt_snd.snd

/-- The `D`-component of the derivative of the evaluation map in the `E`-directions is `u`. -/
theorem fderiv_chartEval_comp_inclE (x : ChartSpace K D E) :
    (fderiv K (fun y : ChartSpace K D E => y.1 y.2.2) x).comp (chartInclE K D E) = x.1 := by
  rw [(hasFDerivAt_chartEval x).fderiv]
  ext b
  simp

theorem projD_comp_fderiv_chartShear_comp_inclE (x : ChartSpace K D E) :
    (chartProjD K D E).comp ((fderiv K (chartShear K D E) x).comp (chartInclE K D E)) =
      x.1 := by
  have h : HasFDerivAt (chartShear K D E)
      ((ContinuousLinearMap.fst K (E →L[K] D) (D × E)).prod
        (((ContinuousLinearMap.fst K D E).comp
            (ContinuousLinearMap.snd K (E →L[K] D) (D × E)) +
          ((x.1).comp ((ContinuousLinearMap.snd K D E).comp
            (ContinuousLinearMap.snd K (E →L[K] D) (D × E))) +
          (ContinuousLinearMap.fst K (E →L[K] D) (D × E)).flip x.2.2)).prod
        ((ContinuousLinearMap.snd K D E).comp
          (ContinuousLinearMap.snd K (E →L[K] D) (D × E))))) x :=
    hasFDerivAt_fst.prodMk
      ((HasFDerivAt.add ((chartProjD K D E).hasFDerivAt (x := x)) (hasFDerivAt_chartEval x)).prodMk
        ((ContinuousLinearMap.snd K D E).comp
          (ContinuousLinearMap.snd K (E →L[K] D) (D × E))).hasFDerivAt)
  rw [h.fderiv]
  ext b
  simp

theorem projD_comp_fderiv_chartShear_symm_comp_inclE (x : ChartSpace K D E) :
    (chartProjD K D E).comp ((fderiv K (chartShear K D E).symm x).comp (chartInclE K D E)) =
      -x.1 := by
  have h : HasFDerivAt (chartShear K D E).symm
      ((ContinuousLinearMap.fst K (E →L[K] D) (D × E)).prod
        (((ContinuousLinearMap.fst K D E).comp
            (ContinuousLinearMap.snd K (E →L[K] D) (D × E)) -
          ((x.1).comp ((ContinuousLinearMap.snd K D E).comp
            (ContinuousLinearMap.snd K (E →L[K] D) (D × E))) +
          (ContinuousLinearMap.fst K (E →L[K] D) (D × E)).flip x.2.2)).prod
        ((ContinuousLinearMap.snd K D E).comp
          (ContinuousLinearMap.snd K (E →L[K] D) (D × E))))) x :=
    hasFDerivAt_fst.prodMk
      ((HasFDerivAt.sub ((chartProjD K D E).hasFDerivAt (x := x)) (hasFDerivAt_chartEval x)).prodMk
        ((ContinuousLinearMap.snd K D E).comp
          (ContinuousLinearMap.snd K (E →L[K] D) (D × E))).hasFDerivAt)
  rw [h.fderiv]
  ext b
  simp

/-- The evaluation map `(u, d, e) ↦ u e` is polynomial. -/
theorem cpolynomialAt_chartEval (x : ChartSpace K D E) :
    CPolynomialAt K (fun y : ChartSpace K D E => y.1 y.2.2) x := by
  have hL : CPolynomialAt K
      (fun y : ChartSpace K D E => ((y.1, y.2.2) : (E →L[K] D) × E)) x :=
    ((ContinuousLinearMap.fst K (E →L[K] D) (D × E)).prod
      ((ContinuousLinearMap.snd K D E).comp
        (ContinuousLinearMap.snd K (E →L[K] D) (D × E)))).cpolynomialAt x
  exact CPolynomialAt.comp (g := fun y : (E →L[K] D) × E => (ContinuousLinearMap.id K _) y.1 y.2)
    (f := fun y : ChartSpace K D E => ((y.1, y.2.2) : (E →L[K] D) × E))
    (cpolynomialAt_bilinear (ContinuousLinearMap.id K (E →L[K] D)) (x.1, x.2.2)) hL

theorem cpolynomialOn_chartShear : CPolynomialOn K (chartShear K D E) Set.univ := by
  intro x _
  have h1 : CPolynomialAt K (fun y : ChartSpace K D E => y.1) x :=
    (ContinuousLinearMap.fst K (E →L[K] D) (D × E)).cpolynomialAt x
  have h2 : CPolynomialAt K (fun y : ChartSpace K D E => y.2.1) x :=
    (chartProjD K D E).cpolynomialAt x
  have h3 : CPolynomialAt K (fun y : ChartSpace K D E => y.2.2) x :=
    ((ContinuousLinearMap.snd K D E).comp
      (ContinuousLinearMap.snd K (E →L[K] D) (D × E))).cpolynomialAt x
  exact cpolynomialAt_pair h1 (cpolynomialAt_pair (h2.add (cpolynomialAt_chartEval x)) h3)

theorem cpolynomialOn_chartShear_symm :
    CPolynomialOn K (chartShear K D E).symm Set.univ := by
  intro x _
  have h1 : CPolynomialAt K (fun y : ChartSpace K D E => y.1) x :=
    (ContinuousLinearMap.fst K (E →L[K] D) (D × E)).cpolynomialAt x
  have h2 : CPolynomialAt K (fun y : ChartSpace K D E => y.2.1) x :=
    (chartProjD K D E).cpolynomialAt x
  have h3 : CPolynomialAt K (fun y : ChartSpace K D E => y.2.2) x :=
    ((ContinuousLinearMap.snd K D E).comp
      (ContinuousLinearMap.snd K (E →L[K] D) (D × E))).cpolynomialAt x
  exact cpolynomialAt_pair h1 (cpolynomialAt_pair (h2.sub (cpolynomialAt_chartEval x)) h3)

/-- The affine slice `u ↦ (c • u, d₀, e₀)` is analytic. -/
theorem analyticAt_chartSlice (c : K) (d₀ : D) (e₀ : E) (u₀ : E →L[K] D) :
    AnalyticAt K (fun u : E →L[K] D => ((c • u, d₀, e₀) : ChartSpace K D E)) u₀ :=
  ((analyticAt_id.const_smul (c := c)).prod (analyticAt_const.prod analyticAt_const))

/-- The transition on forms induced by the chart change is analytic at no point. -/
theorem not_analyticAt_chartShear_pullback
    (hA : ∀ u₀ : E →L[K] D, ¬ AnalyticAt K
      (fun u : E →L[K] D =>
        (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
          (D [⋀^ι]→L[K] F) →L[K] (E [⋀^ι]→L[K] F))) u₀)
    (x : ChartSpace K D E) :
    ¬ AnalyticAt K
      (fun y : ChartSpace K D E =>
        (ContinuousAlternatingMap.compContinuousLinearMapCLM (fderiv K (chartShear K D E) y) :
          (ChartSpace K D E [⋀^ι]→L[K] F) →L[K] (ChartSpace K D E [⋀^ι]→L[K] F))) x := by
  have h := not_analyticAt_pullback_of_slice (F := F) (ι := ι) (chartProjD K D E)
    (chartInclE K D E) (fun y => fderiv K (chartShear K D E) y)
    (fun u => ((1 : K) • u, x.2.1, x.2.2)) x.1 (analyticAt_chartSlice 1 x.2.1 x.2.2 x.1)
    (fun u => by rw [projD_comp_fderiv_chartShear_comp_inclE, one_smul]) (hA x.1)
  simpa only [one_smul] using h

/-- The transition on forms induced by the inverse chart change is analytic at no point. -/
theorem not_analyticAt_chartShear_symm_pullback
    (hA : ∀ u₀ : E →L[K] D, ¬ AnalyticAt K
      (fun u : E →L[K] D =>
        (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
          (D [⋀^ι]→L[K] F) →L[K] (E [⋀^ι]→L[K] F))) u₀)
    (x : ChartSpace K D E) :
    ¬ AnalyticAt K
      (fun y : ChartSpace K D E =>
        (ContinuousAlternatingMap.compContinuousLinearMapCLM
            (fderiv K (chartShear K D E).symm y) :
          (ChartSpace K D E [⋀^ι]→L[K] F) →L[K] (ChartSpace K D E [⋀^ι]→L[K] F))) x := by
  have h := not_analyticAt_pullback_of_slice (F := F) (ι := ι) (chartProjD K D E)
    (chartInclE K D E) (fun y => fderiv K (chartShear K D E).symm y)
    (fun u => ((-1 : K) • u, x.2.1, x.2.2)) (-x.1)
    (analyticAt_chartSlice (-1) x.2.1 x.2.2 (-x.1))
    (fun u => by rw [projD_comp_fderiv_chartShear_symm_comp_inclE, neg_one_smul, neg_neg])
    (hA (-x.1))
  simpa only [neg_one_smul, neg_neg] using h

end AlternatingAnalytic.TangentPullback
