import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Analytic.CPolynomial
import AlternatingAnalytic.Scalar.TangentPullback.Compression

/-!
# A polynomial pullback of an analytic form that is not intrinsically analytic

This is Proposition 6.5(2). Let `B = Alt(D; F)`, `Y = B × D` and `N = L(E, D) × B × E`.
The form `ω₀(m, d) = m ∘ π_D` on `Y` is bounded linear in its point, and the map
`h(u, m, e) = (m, u e)` is polynomial with derivative `Dh(u, m, e)(v, a, b) = (a, v e + u b)`.
Restricting the pulled-back form `h^* ω₀` to the `E`-directions gives `Γ(u, m) = A(u)(m)`.
If `h^* ω₀` were analytic at a point as an `Alt(N; F)`-valued map, then so would be `Γ`, and
its partial derivative in `m`, which is the operator `A(u)`, would be analytic in `u`. As a
`Mult(N; F)`-valued map, `h^* ω₀` is a bounded multilinear expression in `Dh` and `ω₀ ∘ h`,
hence analytic everywhere.
-/

noncomputable section

set_option maxSynthPendingDepth 2

open Filter Topology

namespace AlternatingAnalytic.TangentPullback

variable {K : Type*} [NontriviallyNormedField K]
  {D E F : Type*}
  [NormedAddCommGroup D] [NormedSpace K D]
  [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup F] [NormedSpace K F]
  {ι : Type*} [Fintype ι]

variable (K D E F ι) in
/-- The target `Y = Alt(D; F) × D` of the pullback obstruction. -/
abbrev PullTarget := (D [⋀^ι]→L[K] F) × D

variable (K D E F ι) in
/-- The source `N = L(E, D) × Alt(D; F) × E` of the pullback obstruction. -/
abbrev PullSource := (E →L[K] D) × (D [⋀^ι]→L[K] F) × E

variable (K D E F ι) in
/-- The bounded linear form-valued map `(m, d) ↦ m ∘ π_D` on `Y`. -/
def pullFormCLM : PullTarget K D F ι →L[K] (PullTarget K D F ι [⋀^ι]→L[K] F) :=
  (ContinuousAlternatingMap.compContinuousLinearMapCLM
    (ContinuousLinearMap.snd K (D [⋀^ι]→L[K] F) D)).comp
    (ContinuousLinearMap.fst K (D [⋀^ι]→L[K] F) D)

variable (K D E F ι) in
/-- The analytic form `ω₀(m, d) = m ∘ π_D` on `Y`. -/
def pullForm : PullTarget K D F ι → (PullTarget K D F ι [⋀^ι]→L[K] F) :=
  pullFormCLM K D F ι

omit [Fintype ι] in
theorem pullForm_apply (y : PullTarget K D F ι) :
    pullForm K D F ι y =
      y.1.compContinuousLinearMap (ContinuousLinearMap.snd K (D [⋀^ι]→L[K] F) D) := rfl

variable (K D E F ι) in
/-- The polynomial map `h(u, m, e) = (m, u e)`. -/
def pullMap (x : PullSource K D E F ι) : PullTarget K D F ι := (x.2.1, x.1 x.2.2)

variable (K D E F ι) in
/-- The inclusion `E → N`, `b ↦ (0, 0, b)`. -/
def pullInclE : E →L[K] PullSource K D E F ι :=
  (ContinuousLinearMap.inr K (E →L[K] D) ((D [⋀^ι]→L[K] F) × E)).comp
    (ContinuousLinearMap.inr K (D [⋀^ι]→L[K] F) E)

omit [Fintype ι] in
@[simp]
theorem pullInclE_apply (b : E) : pullInclE K D E F ι b = (0, 0, b) := rfl

variable (K D E F ι) in
/-- The pulled-back form `h^* ω₀` in the product coordinates of `N`. -/
def pulledForm (x : PullSource K D E F ι) : PullSource K D E F ι [⋀^ι]→L[K] F :=
  (pullForm K D F ι (pullMap K D E F ι x)).compContinuousLinearMap (fderiv K (pullMap K D E F ι) x)

theorem hasFDerivAt_pullMap (x : PullSource K D E F ι) :
    HasFDerivAt (pullMap K D E F ι)
      (((ContinuousLinearMap.fst K (D [⋀^ι]→L[K] F) E).comp
          (ContinuousLinearMap.snd K (E →L[K] D) ((D [⋀^ι]→L[K] F) × E))).prod
        ((x.1).comp ((ContinuousLinearMap.snd K (D [⋀^ι]→L[K] F) E).comp
            (ContinuousLinearMap.snd K (E →L[K] D) ((D [⋀^ι]→L[K] F) × E))) +
          (ContinuousLinearMap.fst K (E →L[K] D) ((D [⋀^ι]→L[K] F) × E)).flip x.2.2)) x :=
  HasFDerivAt.prodMk
    (((ContinuousLinearMap.fst K (D [⋀^ι]→L[K] F) E).comp
      (ContinuousLinearMap.snd K (E →L[K] D) ((D [⋀^ι]→L[K] F) × E))).hasFDerivAt (x := x))
    (hasFDerivAt_fst.clm_apply
      ((ContinuousLinearMap.snd K (D [⋀^ι]→L[K] F) E).comp
        (ContinuousLinearMap.snd K (E →L[K] D) ((D [⋀^ι]→L[K] F) × E))).hasFDerivAt)

/-- The `D`-component of `Dh(u, m, e)` in the `E`-directions is `u`. -/
theorem snd_comp_fderiv_pullMap_comp_inclE (x : PullSource K D E F ι) :
    (ContinuousLinearMap.snd K (D [⋀^ι]→L[K] F) D).comp
      ((fderiv K (pullMap K D E F ι) x).comp (pullInclE K D E F ι)) = x.1 := by
  rw [(hasFDerivAt_pullMap x).fderiv]
  ext b
  simp

/-- Restricting `h^* ω₀` to the `E`-directions gives `A(u)(m)`. -/
theorem restrict_pulledForm (x : PullSource K D E F ι) :
    ContinuousAlternatingMap.compContinuousLinearMapCLM (pullInclE K D E F ι) (pulledForm K D E F ι x) =
      x.2.1.compContinuousLinearMap x.1 := by
  have h := snd_comp_fderiv_pullMap_comp_inclE x
  ext v
  simp only [ContinuousAlternatingMap.compContinuousLinearMapCLM_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, pulledForm, pullForm_apply]
  rw [← h]
  rfl

theorem cpolynomialOn_pullMap : CPolynomialOn K (pullMap K D E F ι) Set.univ := by
  intro x _
  have h1 : CPolynomialAt K (fun y : PullSource K D E F ι => y.2.1) x :=
    ((ContinuousLinearMap.fst K (D [⋀^ι]→L[K] F) E).comp
      (ContinuousLinearMap.snd K (E →L[K] D) ((D [⋀^ι]→L[K] F) × E))).cpolynomialAt x
  have hL : CPolynomialAt K
      (fun y : PullSource K D E F ι => ((y.1, y.2.2) : (E →L[K] D) × E)) x :=
    ((ContinuousLinearMap.fst K (E →L[K] D) ((D [⋀^ι]→L[K] F) × E)).prod
      ((ContinuousLinearMap.snd K (D [⋀^ι]→L[K] F) E).comp
        (ContinuousLinearMap.snd K (E →L[K] D) ((D [⋀^ι]→L[K] F) × E)))).cpolynomialAt x
  have h2 : CPolynomialAt K (fun y : PullSource K D E F ι => y.1 y.2.2) x :=
    CPolynomialAt.comp (g := fun y : (E →L[K] D) × E => (ContinuousLinearMap.id K _) y.1 y.2)
      (f := fun y : PullSource K D E F ι => ((y.1, y.2.2) : (E →L[K] D) × E))
      (cpolynomialAt_bilinear (ContinuousLinearMap.id K (E →L[K] D)) (x.1, x.2.2)) hL
  exact cpolynomialAt_pair h1 h2

theorem analyticOnNhd_pullForm : AnalyticOnNhd K (pullForm K D F ι) Set.univ :=
  fun y _ => (pullFormCLM K D F ι).analyticAt y

/-- If the bilinear map `(u, m) ↦ A(u)(m)` is analytic at `(u₀, m₀)`, then `A` is analytic at
`u₀`: its partial derivative in `m` is the operator `A(u)`. -/
theorem analyticAt_of_analyticAt_uncurry [CompleteSpace F] (u₀ : E →L[K] D)
    (m₀ : D [⋀^ι]→L[K] F)
    (hΓ : AnalyticAt K
      (fun q : (E →L[K] D) × (D [⋀^ι]→L[K] F) => q.2.compContinuousLinearMap q.1) (u₀, m₀)) :
    AnalyticAt K
      (fun u : E →L[K] D =>
        (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
          (D [⋀^ι]→L[K] F) →L[K] (E [⋀^ι]→L[K] F))) u₀ := by
  set G := fun q : (E →L[K] D) × (D [⋀^ι]→L[K] F) => q.2.compContinuousLinearMap q.1
  have hder : ∀ q : (E →L[K] D) × (D [⋀^ι]→L[K] F), DifferentiableAt K G q →
      (fderiv K G q).comp (ContinuousLinearMap.inr K (E →L[K] D) (D [⋀^ι]→L[K] F)) =
        ContinuousAlternatingMap.compContinuousLinearMapCLM q.1 := by
    intro q hq
    have h1 : HasFDerivAt (fun m => G (q.1, m))
        ((fderiv K G q).comp (ContinuousLinearMap.inr K (E →L[K] D) (D [⋀^ι]→L[K] F))) q.2 :=
      HasFDerivAt.comp (g := G) (f := fun m => (q.1, m)) q.2 hq.hasFDerivAt
        (hasFDerivAt_prodMk_right q.1 q.2)
    have h2 : HasFDerivAt (fun m => G (q.1, m))
        (ContinuousAlternatingMap.compContinuousLinearMapCLM (F := F) (ι := ι) q.1) q.2 :=
      (ContinuousAlternatingMap.compContinuousLinearMapCLM (F := F) (ι := ι) q.1).hasFDerivAt
    exact h1.unique h2
  have hslice : Tendsto (fun u : E →L[K] D => (u, m₀)) (𝓝 u₀) (𝓝 (u₀, m₀)) :=
    (continuous_id.prodMk continuous_const).tendsto u₀
  have hev : ∀ᶠ u in 𝓝 u₀,
      (fderiv K G (u, m₀)).comp (ContinuousLinearMap.inr K (E →L[K] D) (D [⋀^ι]→L[K] F)) =
        ContinuousAlternatingMap.compContinuousLinearMapCLM u :=
    (hslice.eventually hΓ.eventually_analyticAt).mono fun u hu =>
      hder (u, m₀) hu.differentiableAt
  have hfd : AnalyticAt K (fun u : E →L[K] D =>
      (fderiv K G (u, m₀)).comp (ContinuousLinearMap.inr K (E →L[K] D) (D [⋀^ι]→L[K] F)))
      u₀ :=
    (ContinuousLinearMap.analyticAt (𝕜 := K)
      (E := (E →L[K] D) × (D [⋀^ι]→L[K] F) →L[K] (E [⋀^ι]→L[K] F))
      (F := (D [⋀^ι]→L[K] F) →L[K] (E [⋀^ι]→L[K] F))
      ((ContinuousLinearMap.compL K (D [⋀^ι]→L[K] F) ((E →L[K] D) × (D [⋀^ι]→L[K] F))
        (E [⋀^ι]→L[K] F)).flip (ContinuousLinearMap.inr K (E →L[K] D) (D [⋀^ι]→L[K] F)))
      _).comp (AnalyticAt.comp (g := fderiv K G) (f := fun u : E →L[K] D => (u, m₀))
        hΓ.fderiv (analyticAt_id.prod analyticAt_const))
  exact hfd.congr hev

/-- The pulled-back form `h^* ω₀` is analytic at no point as an `Alt(N; F)`-valued map. -/
theorem not_analyticAt_pulledForm [CompleteSpace F]
    (hA : ∀ u₀ : E →L[K] D, ¬ AnalyticAt K
      (fun u : E →L[K] D =>
        (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
          (D [⋀^ι]→L[K] F) →L[K] (E [⋀^ι]→L[K] F))) u₀)
    (x₀ : PullSource K D E F ι) : ¬ AnalyticAt K (pulledForm K D E F ι) x₀ := by
  intro ha
  apply hA x₀.1
  apply analyticAt_of_analyticAt_uncurry x₀.1 x₀.2.1
  have hs : AnalyticAt K
      (fun q : (E →L[K] D) × (D [⋀^ι]→L[K] F) => ((q.1, q.2, x₀.2.2) : PullSource K D E F ι))
      (x₀.1, x₀.2.1) :=
    analyticAt_fst.prod (analyticAt_snd.prod analyticAt_const)
  have hc := (ContinuousLinearMap.analyticAt (𝕜 := K)
    (E := PullSource K D E F ι [⋀^ι]→L[K] F) (F := E [⋀^ι]→L[K] F)
    (ContinuousAlternatingMap.compContinuousLinearMapCLM (pullInclE K D E F ι)) _).comp
      (ha.comp hs)
  simpa only [Function.comp_def, restrict_pulledForm] using hc

/-- After inclusion into `Mult(N; F)`, the pulled-back form `h^* ω₀` is analytic everywhere. -/
theorem analyticOnNhd_pulledForm_toContinuousMultilinearMap [CompleteSpace D] [CompleteSpace F] :
    AnalyticOnNhd K (fun x => (pulledForm K D E F ι x).toContinuousMultilinearMap) Set.univ := by
  intro x _
  have hh : AnalyticAt K (pullMap K D E F ι) x :=
    (cpolynomialOn_pullMap x (Set.mem_univ x)).analyticAt
  have hω : AnalyticAt K (fun y => (pullForm K D F ι (pullMap K D E F ι y)).toContinuousMultilinearMap) x :=
    (ContinuousLinearMap.analyticAt (𝕜 := K)
      (E := PullTarget K D F ι [⋀^ι]→L[K] F)
      (F := ContinuousMultilinearMap K (fun _ : ι => PullTarget K D F ι) F)
      (ContinuousAlternatingMap.toContinuousMultilinearMapCLM K) _).comp
      ((pullFormCLM K D F ι).analyticAt _ |>.comp hh)
  have hd : AnalyticAt K (fun y => fun _ : ι => fderiv K (pullMap K D E F ι) y) x :=
    AnalyticAt.pi fun _ => hh.fderiv
  exact (ContinuousMultilinearMap.analyticAt_uncurry_compContinuousLinearMap).comp
    (hd.prod hω)

end AlternatingAnalytic.TangentPullback
