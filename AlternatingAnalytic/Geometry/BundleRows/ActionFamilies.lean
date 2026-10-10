import AlternatingAnalytic.Geometry.AnalyticAlternatingBundleMorphism
import AlternatingAnalytic.Analysis.L1Families
import AlternatingAnalytic.Analysis.CZeroFamilies
import AlternatingAnalytic.Analysis.AlternatingActionRegularity
import AlternatingAnalytic.Analysis.FiniteCoordinateDomain
import AlternatingAnalytic.Geometry.BundleRows.EquivalentSphericalNorm

/-!
# Family preservation for the alternating action, setting by setting

The hypothesis of `contMDiffVectorBundle_alternating_of_family` and
`alternatingBundleHom_of_family` is that the model action `alternatingMapAction` takes analytic
(or `C^n`) families to analytic (or `C^n`) families. It holds in each setting of Corollary 4.6:
`k! ≠ 0`, a target with an equivalent spherically complete ultrametric norm, a source with finite
coordinates, a base that is a retract of `c₀`, and every finite smoothness order. The first lemma
passes from the model space to manifolds.
-/

open scoped Manifold ContDiff ZeroAtInfty

namespace AlternatingAnalytic.BundleRows

/-- Local analytic family preservation in the model space gives manifold family preservation. -/
theorem glue_contMDiffOn_alternatingMapAction
    {K P M E E' F F' : Type*} [NontriviallyNormedField K]
    [NormedAddCommGroup P] [NormedSpace K P]
    [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup E'] [NormedSpace K E']
    [NormedAddCommGroup F] [NormedSpace K F]
    [NormedAddCommGroup F'] [NormedSpace K F']
    [TopologicalSpace M] [ChartedSpace P M] [IsManifold 𝓘(K, P) ω M] (k : ℕ)
    (hloc : ∀ {V : Set P} {γ : P → (E' →L[K] E) × (F →L[K] F')}, IsOpen V →
      AnalyticOnNhd K γ V → AnalyticOnNhd K (alternatingMapAction k ∘ γ) V)
    {U : Set M} (hU : IsOpen U)
    {γ : M → (E' →L[K] E) × (F →L[K] F')}
    (hγ : ContMDiffOn 𝓘(K, P) 𝓘(K, (E' →L[K] E) × (F →L[K] F')) ω γ U) :
    ContMDiffOn 𝓘(K, P)
      𝓘(K, (E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F'))
      ω (alternatingMapAction k ∘ γ) U := by
  intro x hx
  have hV : IsOpen ((extChartAt 𝓘(K, P) x).target ∩
      (extChartAt 𝓘(K, P) x).symm ⁻¹' U) :=
    (continuousOn_extChartAt_symm x).isOpen_inter_preimage
      (isOpen_extChartAt_target x) hU
  have hxV : extChartAt 𝓘(K, P) x x ∈
      (extChartAt 𝓘(K, P) x).target ∩ (extChartAt 𝓘(K, P) x).symm ⁻¹' U := by
    simpa only [mfld_simps] using hx
  have hγc : ContDiffOn K ω (γ ∘ (extChartAt 𝓘(K, P) x).symm)
      ((extChartAt 𝓘(K, P) x).target ∩ (extChartAt 𝓘(K, P) x).symm ⁻¹' U) := by
    simpa [chartAt_self_eq, mfld_simps] using (contMDiffOn_iff.mp hγ).2 x 0
  have ha := hloc hV (hV.analyticOn_iff_analyticOnNhd.mp
      ((contDiffOn_omega_iff_analyticOn hV.uniqueDiffOn).mp hγc))
  have hc : ContMDiffOn 𝓘(K, P)
      𝓘(K, (E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F'))
      ω ((alternatingMapAction k ∘ γ) ∘ (extChartAt 𝓘(K, P) x).symm)
      ((extChartAt 𝓘(K, P) x).target ∩ (extChartAt 𝓘(K, P) x).symm ⁻¹' U) :=
    contMDiffOn_iff_contDiffOn.mpr (ha.contDiffOn hV.uniqueDiffOn)
  apply ContMDiffAt.contMDiffWithinAt
  apply contMDiffAt_iff_source.mpr
  exact (hc.contMDiffAt (hV.mem_nhds hxV)).contMDiffWithinAt

/-- Global analyticity of the action gives local family preservation. -/
theorem hloc_of_global
    {K P E E' F F' : Type*} [NontriviallyNormedField K]
    [NormedAddCommGroup P] [NormedSpace K P]
    [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup E'] [NormedSpace K E']
    [NormedAddCommGroup F] [NormedSpace K F]
    [NormedAddCommGroup F'] [NormedSpace K F'] (k : ℕ)
    (h : ∀ z : (E' →L[K] E) × (F →L[K] F'), AnalyticAt K (alternatingMapAction k) z)
    {V : Set P} {γ : P → (E' →L[K] E) × (F →L[K] F')} (_ : IsOpen V)
    (hγ : AnalyticOnNhd K γ V) : AnalyticOnNhd K (alternatingMapAction k ∘ γ) V :=
  fun x hx => (h (γ x)).comp (hγ x hx)

/-- Local family preservation over a bounded linear retract of `c₀(I, K)`. -/
theorem hloc_c0_retract
    {K I P E E' F F' : Type*} [NontriviallyNormedField K]
    [TopologicalSpace I] [DiscreteTopology I]
    [NormedAddCommGroup P] [NormedSpace K P]
    [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup E'] [NormedSpace K E']
    [NormedAddCommGroup F] [NormedSpace K F]
    [NormedAddCommGroup F'] [NormedSpace K F'] [CompleteSpace F'] [IsUltrametricDist F']
    (k : ℕ) (i : P →L[K] C₀(I, K)) (r : C₀(I, K) →L[K] P)
    (hri : r.comp i = ContinuousLinearMap.id K P)
    {V : Set P} {γ : P → (E' →L[K] E) × (F →L[K] F')} (_ : IsOpen V)
    (hγ : AnalyticOnNhd K γ V) : AnalyticOnNhd K (alternatingMapAction k ∘ γ) V := by
  have hri_apply (x : P) : r (i x) = x := DFunLike.congr_fun hri x
  have hpull : IsAdmissibleOn k (γ ∘ r) (r ⁻¹' V) :=
    isAdmissibleOn_of_c0 k (hγ.comp (r.analyticOnNhd _) (fun _ hx => hx))
  have hmaps : Set.MapsTo i V (r ⁻¹' V) := by
    intro x hx
    change r (i x) ∈ V
    rwa [hri_apply]
  have hcomp : (γ ∘ r) ∘ i = γ := by
    funext x
    exact congrArg γ (hri_apply x)
  exact (by simpa only [hcomp] using hpull.reparam (i.analyticOnNhd V) hmaps :
    IsAdmissibleOn k γ V).2

/-- Finite continuous coordinates give a basis with continuous coordinates. -/
theorem hasBoundedLift_of_equiv {K E E' F : Type*} [NontriviallyNormedField K]
    [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup E'] [NormedSpace K E']
    [NormedAddCommGroup F] [NormedSpace K F]
    {d : ℕ} (c : E ≃L[K] (Fin d → K)) (k : ℕ) :
    LiftCriterion.HasBoundedLift K (Fin k) E E' F := by
  let b : Module.Basis (Fin d) K E := (Pi.basisFun K (Fin d)).map c.symm.toLinearEquiv
  have hb : ∀ i, Continuous (b.coord i) := by
    intro i
    have : ⇑(b.coord i) = fun x => c x i := by
      funext x
      simp [b, Module.Basis.coord]
    rw [this]
    exact (continuous_apply i).comp c.continuous
  exact hasBoundedLift_of_finiteCoordinateDomain b hb k


/-- Local family preservation when `k!` is invertible in `K`. -/
theorem hloc_factorial
    {K P E E' F F' : Type*} [NontriviallyNormedField K]
    [NormedAddCommGroup P] [NormedSpace K P]
    [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup E'] [NormedSpace K E']
    [NormedAddCommGroup F] [NormedSpace K F]
    [NormedAddCommGroup F'] [NormedSpace K F'] (k : ℕ) (hk : (k.factorial : K) ≠ 0)
    {V : Set P} {γ : P → (E' →L[K] E) × (F →L[K] F')} (hV : IsOpen V)
    (hγ : AnalyticOnNhd K γ V) : AnalyticOnNhd K (alternatingMapAction k ∘ γ) V :=
  hloc_of_global k (fun z ↦
    (cpolynomialAt_alternatingMapAction_of_factorial_ne_zero k hk z).analyticAt) hV hγ

/-- Local family preservation for a source with finite continuous coordinates. -/
theorem hloc_finiteSource
    {K P E E' F F' : Type*} [NontriviallyNormedField K]
    [NormedAddCommGroup P] [NormedSpace K P]
    [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup E'] [NormedSpace K E']
    [NormedAddCommGroup F] [NormedSpace K F]
    [NormedAddCommGroup F'] [NormedSpace K F'] (k : ℕ) {d : ℕ} (c : E' ≃L[K] (Fin d → K))
    {V : Set P} {γ : P → (E' →L[K] E) × (F →L[K] F')} (hV : IsOpen V)
    (hγ : AnalyticOnNhd K γ V) : AnalyticOnNhd K (alternatingMapAction k ∘ γ) V :=
  hloc_of_global k (fun z ↦ (cpolynomialAt_alternatingMapAction_of_boundedLift k
    (hasBoundedLift_of_equiv c k) z).analyticAt) hV hγ

/-- Family preservation at every finite smoothness order and at `C^∞`. -/
theorem smooth_family
    {K P M E E' F F' : Type*} [NontriviallyNormedField K]
    [NormedAddCommGroup P] [NormedSpace K P]
    [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup E'] [NormedSpace K E']
    [NormedAddCommGroup F] [NormedSpace K F]
    [NormedAddCommGroup F'] [NormedSpace K F']
    [TopologicalSpace M] [ChartedSpace P M] (k : ℕ) (n : ℕ∞)
    {U : Set M} (_ : IsOpen U)
    {γ : M → (E' →L[K] E) × (F →L[K] F')}
    (hγ : ContMDiffOn 𝓘(K, P) 𝓘(K, (E' →L[K] E) × (F →L[K] F')) n γ U) :
    ContMDiffOn 𝓘(K, P)
      𝓘(K, (E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F'))
      n (alternatingMapAction k ∘ γ) U :=
  (contDiff_alternatingMapAction k n).contMDiff.comp_contMDiffOn hγ


/-- Local family preservation when the coefficient target admits an equivalent spherically
complete ultrametric norm. -/
theorem hloc_equivalentSphericalNorm
    {K P E E' F F' : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    [NormedAddCommGroup P] [NormedSpace K P]
    [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup E'] [NormedSpace K E']
    [NormedAddCommGroup F] [NormedSpace K F]
    [NormedAddCommGroup F'] [NormedSpace K F'] (k : ℕ)
    (hF : ∃ q : Seminorm K F,
      (∀ x y, q (x + y) ≤ max (q x) (q y)) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ x, ‖x‖ ≤ C * q x) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ x, q x ≤ C * ‖x‖) ∧
      (∀ S : Set (F × ℝ), S.Nonempty →
        (∀ p ∈ S, ∀ p' ∈ S, ∃ z, q (z - p.1) ≤ p.2 ∧ q (z - p'.1) ≤ p'.2) →
        ∃ z, ∀ p ∈ S, q (z - p.1) ≤ p.2))
    {V : Set P} {γ : P → (E' →L[K] E) × (F →L[K] F')} (hV : IsOpen V)
    (hγ : AnalyticOnNhd K γ V) : AnalyticOnNhd K (alternatingMapAction k ∘ γ) V := by
  obtain ⟨q, hmax, hlow, hup, hsph⟩ := hF
  exact hloc_of_global k (fun z ↦
    (EquivalentSphericalNorm.cpolynomialAt_alternatingMapAction_of_equivalentSphericalNorm
      q hmax hlow hup hsph k z).analyticAt) hV hγ

end AlternatingAnalytic.BundleRows
