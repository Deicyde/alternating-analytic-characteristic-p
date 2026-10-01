import AlternatingAnalytic.Analysis.ShearCounterexample
import AlternatingAnalytic.Geometry.AnalyticAlternatingBundle
import AlternatingAnalytic.Analysis.AlternatingActionRegularity

/-!
# The analytic alternating bundle over a Banach base can fail to be analytic

This is the bundle form of Proposition `fam:prop:shear` of `paper/charp.tex`
(Corollary `fam:cor:banach-base-failure`). The base is the operator space
`E →L[K] D`, a manifold with one chart. Over it, the shear family defines a
vector bundle core with fiber `D × E` and two global trivializations whose
transition is `shear u`. This bundle is analytic, as is the trivial bundle with
fiber `F`. The coordinate change between the two induced trivializations of the
alternating-map bundle is pullback by the shear. If it were analytic at the
zero parameter, the compression of `fam:prop:shear` would make the original
pullback analytic there.

In characteristic `p` and degree `k ≥ p`, the Banach counterexample therefore
shows that the actual alternating bundle of two analytic bundles, with
Mathlib's existing topology, need not be analytic. The hypothesis of
`contMDiffVectorBundle_alternating_of_finiteCoordinates` cannot be removed.
-/

noncomputable section

open Bundle Set
open scoped Bundle Manifold ContDiff

namespace AlternatingAnalytic

universe u

variable {K : Type*} [NontriviallyNormedField K]
  {D E F : Type*}
  [NormedAddCommGroup D] [NormedSpace K D]
  [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup F] [NormedSpace K F]

/-- Composition of shears adds their parameters. -/
theorem shear_shear_apply (u v : E →L[K] D) (z : D × E) :
    shear u (shear v z) = shear (u + v) z := by
  ext
  · simp only [shear_apply, add_apply]
    abel
  · simp

/-- The parameter weight of the two charts of the shear bundle. -/
def shearChartWeight (i : Bool) : K := if i then 1 else 0

/-- The shear vector bundle core over the operator space `E →L[K] D`. Both charts
are global, and the transition from chart `i` to chart `j` is
`shear ((w j - w i) • u)`, where `w false = 0` and `w true = 1`. -/
def shearBundleCore : VectorBundleCore K (E →L[K] D) (D × E) Bool where
  baseSet _ := univ
  isOpen_baseSet _ := isOpen_univ
  indexAt _ := false
  mem_baseSet_at _ := mem_univ _
  coordChange i j u := shear ((shearChartWeight (K := K) j - shearChartWeight i) • u)
  coordChange_self i u _ v := by simp
  continuousOn_coordChange i j :=
    (continuous_const.add (shearLinear.continuous.comp (continuous_const_smul _))).continuousOn
  coordChange_comp i j k u _ v := by
    rw [shear_shear_apply, ← add_smul]
    congr 3
    ring

@[simp]
theorem shearBundleCore_coordChange (i j : Bool) (u : E →L[K] D) :
    (shearBundleCore (K := K) (D := D) (E := E)).coordChange i j u =
      shear ((shearChartWeight (K := K) j - shearChartWeight i) • u) := rfl

/-- The transition from chart `false` to chart `true` is the shear itself. -/
theorem shearBundleCore_coordChange_false_true (u : E →L[K] D) :
    (shearBundleCore (K := K) (D := D) (E := E)).coordChange false true u = shear u := by
  simp [shearChartWeight]

/-- The shear bundle core is analytic: its transitions are affine in the parameter. -/
instance shearBundleCore_isContMDiff :
    (shearBundleCore (K := K) (D := D) (E := E)).IsContMDiff 𝓘(K, E →L[K] D) ω where
  contMDiffOn_coordChange i j := by
    have h₁ : ContDiff K ω (fun u : E →L[K] D =>
        shearLinear ((shearChartWeight (K := K) j - shearChartWeight i) • u)) :=
      (shearLinear (K := K) (D := D) (E := E)).contDiff.comp
        (contDiff_const_smul (shearChartWeight (K := K) j - shearChartWeight i))
    have h : ContDiff K ω (fun u : E →L[K] D =>
        shear ((shearChartWeight (K := K) j - shearChartWeight i) • u)) := by
      simp only [shear]
      exact contDiff_const.add h₁
    exact h.contMDiff.contMDiffOn

instance shearBundleCore_memTrivializationAtlas (i : Bool) :
    MemTrivializationAtlas ((shearBundleCore (K := K) (D := D) (E := E)).localTriv i) :=
  ⟨⟨i, rfl⟩⟩

/-- A trivialization changes coordinates with itself by the identity. -/
theorem Trivialization.coordChangeL_self_eq {B F' : Type*} [TopologicalSpace B]
    [NormedAddCommGroup F'] [NormedSpace K F'] {E' : B → Type*}
    [∀ x, AddCommGroup (E' x)] [∀ x, Module K (E' x)]
    [TopologicalSpace (TotalSpace F' E')]
    (e : Trivialization F' (π F' E')) [e.IsLinear K] {b : B} (hb : b ∈ e.baseSet) :
    (e.coordChangeL K e b : F' →L[K] F') = ContinuousLinearMap.id K F' := by
  ext y
  rw [ContinuousLinearEquiv.coe_coe, e.coordChangeL_apply e ⟨hb, hb⟩, e.apply_mk_symm hb]
  rfl

section Bundle

variable (K D E F)

/-- The trivial analytic bundle over the shear base, with fiber `F`. -/
abbrev ShearTargetBundle : (E →L[K] D) → Type _ := Bundle.Trivial (E →L[K] D) F

end Bundle

/-- **Bundle form of the shear obstruction.** The alternating bundle of the shear
bundle and the trivial bundle has the shear pullback as a coordinate change. If the
original pullback is not analytic at the zero parameter, this bundle is not
analytic. The source bundle and the target bundle are both analytic. -/
theorem not_contMDiffVectorBundle_alternating_shearBundle (k : ℕ)
    (hbad : ¬ AnalyticAt K
      (fun v : D →L[K] D =>
        ContinuousAlternatingMap.compContinuousLinearMapCLM (F := F) (ι := Fin k)
          (shear v)) 0) :
    ¬ ContMDiffVectorBundle ω ((D × D) [⋀^Fin k]→L[K] F)
      (fun u ↦ (shearBundleCore (K := K) (D := D) (E := D)).Fiber u [⋀^Fin k]→L[K]
        ShearTargetBundle K D D F u) 𝓘(K, D →L[K] D) := by
  intro hbundle
  let Z := shearBundleCore (K := K) (D := D) (E := D)
  let e₂ : Trivialization F (π F (ShearTargetBundle K D D F)) :=
    trivializationAt F (ShearTargetBundle K D D F) 0
  have he₂ : ∀ b, b ∈ e₂.baseSet := fun b ↦ by
    simp [e₂, Bundle.Trivial.trivialization]
  have hc := contMDiffOn_coordChangeL (IB := 𝓘(K, D →L[K] D)) (n := ω)
    ((Z.localTriv true).continuousAlternatingMap K (Fin k) e₂)
    ((Z.localTriv false).continuousAlternatingMap K (Fin k) e₂)
  have hbase : ∀ b : D →L[K] D,
      b ∈ (Z.localTriv true).baseSet ∩ e₂.baseSet ∩
        ((Z.localTriv false).baseSet ∩ e₂.baseSet) := fun b ↦
    ⟨⟨mem_univ _, he₂ b⟩, mem_univ _, he₂ b⟩
  have heq : ∀ b : D →L[K] D,
      (((Z.localTriv true).continuousAlternatingMap K (Fin k) e₂).coordChangeL K
          ((Z.localTriv false).continuousAlternatingMap K (Fin k) e₂) b :
          ((D × D) [⋀^Fin k]→L[K] F) →L[K] ((D × D) [⋀^Fin k]→L[K] F)) =
        ContinuousAlternatingMap.compContinuousLinearMapCLM (shear b) := by
    intro b
    rw [coordChangeL_continuousAlternatingMap_eq_alternatingMapAction k _ _ _ _ b (hbase b),
      Trivialization.coordChangeL_self_eq e₂ (he₂ b)]
    have h₁ : ((Z.localTriv false).coordChangeL K (Z.localTriv true) b : D × D →L[K] D × D) =
        shear b := by
      refine ContinuousLinearMap.ext fun v ↦ ?_
      rw [ContinuousLinearEquiv.coe_coe,
        Z.localTriv_coordChange_eq false true (b := b) ⟨mem_univ _, mem_univ _⟩ v,
        shearBundleCore_coordChange_false_true]
    rw [h₁, alternatingMapAction_id_right]
  have hsets : ((Z.localTriv true).continuousAlternatingMap K (Fin k) e₂).baseSet ∩
      ((Z.localTriv false).continuousAlternatingMap K (Fin k) e₂).baseSet = univ := by
    ext b
    simpa [Trivialization.baseSet_continuousAlternatingMap] using hbase b
  rw [hsets] at hc
  have hcd : ContDiff K ω (fun b : D →L[K] D =>
      (ContinuousAlternatingMap.compContinuousLinearMapCLM (F := F) (ι := Fin k)
        (shear b))) := by
    rw [← contMDiff_iff_contDiff, ← contMDiffOn_univ]
    exact hc.congr fun b _ ↦ (heq b).symm
  exact hbad hcd.contDiffAt.analyticAt

/-- Over every nontrivially normed field of characteristic `p`, in every degree
`k ≥ p`, there are Banach spaces `E` and `F` such that, over the Banach base
`E →L[K] E`, the shear bundle and the trivial bundle with fiber `F` are analytic
but their alternating-map bundle is not. -/
theorem exists_banach_base_alternatingBundle_not_analytic
    (K : Type u) [NontriviallyNormedField K] (p k : ℕ) (hp : p.Prime)
    [CharP K p] (hpk : p ≤ k) :
    ∃ (E F : Type u) (normedGroupE : NormedAddCommGroup E)
      (normedGroupF : NormedAddCommGroup F),
      let : NormedAddCommGroup E := normedGroupE
      let : NormedAddCommGroup F := normedGroupF
      ∃ (normedSpaceE : NormedSpace K E) (normedSpaceF : NormedSpace K F),
        let : NormedSpace K E := normedSpaceE
        let : NormedSpace K F := normedSpaceF
        ∃ (_ : CompleteSpace E) (_ : CompleteSpace F),
          ContMDiffVectorBundle ω (E × E) (shearBundleCore (K := K) (D := E) (E := E)).Fiber
              𝓘(K, E →L[K] E) ∧
            ContMDiffVectorBundle ω F (ShearTargetBundle K E E F) 𝓘(K, E →L[K] E) ∧
            ¬ ContMDiffVectorBundle ω ((E × E) [⋀^Fin k]→L[K] F)
              (fun u ↦ (shearBundleCore (K := K) (D := E) (E := E)).Fiber u [⋀^Fin k]→L[K]
                ShearTargetBundle K E E F u) 𝓘(K, E →L[K] E) := by
  obtain ⟨E, F, gE, gF, nE, nF, cE, cF, _, _, _, hbad⟩ :=
    exists_banach_shear_counterexample K p k hp hpk
  let : NormedAddCommGroup E := gE
  let : NormedAddCommGroup F := gF
  let : NormedSpace K E := nE
  let : NormedSpace K F := nF
  refine ⟨E, F, gE, gF, nE, nF, cE, cF, inferInstance, inferInstance, ?_⟩
  exact not_contMDiffVectorBundle_alternating_shearBundle (K := K) (D := E) (F := F) k hbad

end AlternatingAnalytic
