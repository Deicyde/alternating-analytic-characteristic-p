import AlternatingAnalytic.Geometry.AlternatingBundleShearCounterexample

/-!
# The shear bundle realization over `L(E, D)`

The bundle paragraph after Proposition 6.4. The base is `E →L[K] D`, the fiber is `D × E` with
the maximum norm, and `u₀` is any point where `A^k : u ↦ u^*` is not analytic. If two global
charts of a vector bundle core change coordinates by `shear u`, the induced alternating
trivializations change by pullback along `shear u`. If the alternating bundle were analytic,
this pullback would be analytic, and the compression identity of Proposition 6.4 would make
`u ↦ u^*` analytic at `u₀`. This generalizes
`not_contMDiffVectorBundle_alternating_shearBundle`, which has base `L(D, D)` and `u₀ = 0`.
-/

noncomputable section

open Bundle Set
open scoped Bundle Manifold ContDiff

namespace AlternatingAnalytic

variable {K : Type*} [NontriviallyNormedField K]
  {D E F : Type*}
  [NormedAddCommGroup D] [NormedSpace K D]
  [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup F] [NormedSpace K F]
  {ι : Type*}

/-- A vector bundle core over `E →L[K] D` whose transitions are shears at weighted
parameters `(w j - w i) • u` is analytic. -/
theorem vectorBundleCore_isContMDiff_of_coordChange_eq_shear
    (Z : VectorBundleCore K (E →L[K] D) (D × E) ι) (w : ι → K)
    (h : ∀ i j u, Z.coordChange i j u = shear ((w j - w i) • u)) :
    Z.IsContMDiff 𝓘(K, E →L[K] D) ω where
  contMDiffOn_coordChange i j := by
    have h₁ : ContDiff K ω (fun u : E →L[K] D => shear ((w j - w i) • u)) := by
      simp only [shear]
      exact contDiff_const.add
        ((shearLinear (K := K) (D := D) (E := E)).contDiff.comp (contDiff_const_smul _))
    exact (h₁.contMDiff.contMDiffOn).congr fun u _ ↦ h i j u

/-- A vector bundle core over `E →L[K] D` with shear transitions is an analytic vector
bundle. -/
theorem vectorBundleCore_contMDiffVectorBundle_of_coordChange_eq_shear
    (Z : VectorBundleCore K (E →L[K] D) (D × E) ι) (w : ι → K)
    (h : ∀ i j u, Z.coordChange i j u = shear ((w j - w i) • u)) :
    ContMDiffVectorBundle ω (D × E) Z.Fiber 𝓘(K, E →L[K] D) := by
  have := vectorBundleCore_isContMDiff_of_coordChange_eq_shear Z w h
  infer_instance

/-- If two global charts of a vector bundle core over `E →L[K] D` change coordinates by
`shear u`, and the pullback `u ↦ u^*` is not analytic at `u₀`, then the alternating bundle
of the core and the trivial `F`-bundle is not analytic. -/
theorem not_contMDiffVectorBundle_alternating_of_coordChange_eq_shear (k : ℕ)
    (Z : VectorBundleCore K (E →L[K] D) (D × E) ι) (i j : ι)
    (hi : Z.baseSet i = univ) (hj : Z.baseSet j = univ)
    (hZ : ∀ u, Z.coordChange i j u = shear u) (u₀ : E →L[K] D)
    (hA : ¬ AnalyticAt K
      (fun u : E →L[K] D =>
        (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
          (D [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F))) u₀) :
    ¬ ContMDiffVectorBundle ω ((D × E) [⋀^Fin k]→L[K] F)
      (fun u ↦ Z.Fiber u [⋀^Fin k]→L[K] Bundle.Trivial (E →L[K] D) F u)
      𝓘(K, E →L[K] D) := by
  intro hbundle
  have : MemTrivializationAtlas (Z.localTriv i) := ⟨⟨i, rfl⟩⟩
  have : MemTrivializationAtlas (Z.localTriv j) := ⟨⟨j, rfl⟩⟩
  let e₂ : Trivialization F (π F (Bundle.Trivial (E →L[K] D) F)) :=
    trivializationAt F (Bundle.Trivial (E →L[K] D) F) 0
  have he₂ : ∀ b, b ∈ e₂.baseSet := fun b ↦ by
    simp [e₂, Bundle.Trivial.trivialization]
  have hi' : ∀ b, b ∈ (Z.localTriv i).baseSet := fun b ↦ by
    change b ∈ Z.baseSet i; rw [hi]; exact mem_univ _
  have hj' : ∀ b, b ∈ (Z.localTriv j).baseSet := fun b ↦ by
    change b ∈ Z.baseSet j; rw [hj]; exact mem_univ _
  have hc := contMDiffOn_coordChangeL (IB := 𝓘(K, E →L[K] D)) (n := ω)
    ((Z.localTriv j).continuousAlternatingMap K (Fin k) e₂)
    ((Z.localTriv i).continuousAlternatingMap K (Fin k) e₂)
  have hbase : ∀ b : E →L[K] D,
      b ∈ (Z.localTriv j).baseSet ∩ e₂.baseSet ∩
        ((Z.localTriv i).baseSet ∩ e₂.baseSet) := fun b ↦
    ⟨⟨hj' b, he₂ b⟩, hi' b, he₂ b⟩
  have heq : ∀ b : E →L[K] D,
      (((Z.localTriv j).continuousAlternatingMap K (Fin k) e₂).coordChangeL K
          ((Z.localTriv i).continuousAlternatingMap K (Fin k) e₂) b :
          ((D × E) [⋀^Fin k]→L[K] F) →L[K] ((D × E) [⋀^Fin k]→L[K] F)) =
        ContinuousAlternatingMap.compContinuousLinearMapCLM (shear b) := by
    intro b
    rw [coordChangeL_continuousAlternatingMap_eq_alternatingMapAction k _ _ _ _ b (hbase b),
      Trivialization.coordChangeL_self_eq e₂ (he₂ b)]
    have h₁ : ((Z.localTriv i).coordChangeL K (Z.localTriv j) b : D × E →L[K] D × E) =
        shear b := by
      refine ContinuousLinearMap.ext fun v ↦ ?_
      rw [ContinuousLinearEquiv.coe_coe,
        Z.localTriv_coordChange_eq i j (b := b) ⟨hi' b, hj' b⟩ v, hZ]
    rw [h₁, alternatingMapAction_id_right]
  have hsets : ((Z.localTriv j).continuousAlternatingMap K (Fin k) e₂).baseSet ∩
      ((Z.localTriv i).continuousAlternatingMap K (Fin k) e₂).baseSet = univ := by
    ext b
    simpa [Trivialization.baseSet_continuousAlternatingMap] using hbase b
  rw [hsets] at hc
  have hcd : ContDiff K ω (fun b : E →L[K] D =>
      (ContinuousAlternatingMap.compContinuousLinearMapCLM (F := F) (ι := Fin k)
        (shear b))) := by
    rw [← contMDiff_iff_contDiff, ← contMDiffOn_univ]
    exact hc.congr fun b _ ↦ (heq b).symm
  exact not_analyticAt_shear_pullback (ι := Fin k) u₀ hA hcd.contDiffAt.analyticAt

/-- Let a vector bundle core over `E →L[K] D` have transitions `shear ((w j - w i) • u)` and two
global charts `i, j` with `w j - w i = 1`. If `u ↦ u^*` is not analytic at `u₀`, the core and the
trivial `F`-bundle are analytic but their alternating bundle is not. -/
theorem shearBundle_realization (k : ℕ)
    (Z : VectorBundleCore K (E →L[K] D) (D × E) ι) (w : ι → K)
    (h : ∀ i j u, Z.coordChange i j u = shear ((w j - w i) • u))
    (i j : ι) (hi : Z.baseSet i = univ) (hj : Z.baseSet j = univ) (hw : w j - w i = 1)
    (u₀ : E →L[K] D)
    (hA : ¬ AnalyticAt K
      (fun u : E →L[K] D =>
        (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
          (D [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F))) u₀) :
    ContMDiffVectorBundle ω (D × E) Z.Fiber 𝓘(K, E →L[K] D) ∧
    ContMDiffVectorBundle ω F (Bundle.Trivial (E →L[K] D) F) 𝓘(K, E →L[K] D) ∧
    ¬ ContMDiffVectorBundle ω ((D × E) [⋀^Fin k]→L[K] F)
      (fun u ↦ Z.Fiber u [⋀^Fin k]→L[K] Bundle.Trivial (E →L[K] D) F u)
      𝓘(K, E →L[K] D) :=
  ⟨vectorBundleCore_contMDiffVectorBundle_of_coordChange_eq_shear Z w h, inferInstance,
    not_contMDiffVectorBundle_alternating_of_coordChange_eq_shear k Z i j hi hj
      (fun u ↦ by rw [h, hw, one_smul]) u₀ hA⟩

/-- `shearBundleCore` realizes the obstruction at every `u₀` where `u ↦ u^*` is not
analytic. -/
theorem shearBundleCore_realization (k : ℕ) (u₀ : E →L[K] D)
    (hA : ¬ AnalyticAt K
      (fun u : E →L[K] D =>
        (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
          (D [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F))) u₀) :
    ContMDiffVectorBundle ω (D × E) (shearBundleCore (K := K) (D := D) (E := E)).Fiber
      𝓘(K, E →L[K] D) ∧
    ContMDiffVectorBundle ω F (Bundle.Trivial (E →L[K] D) F) 𝓘(K, E →L[K] D) ∧
    ¬ ContMDiffVectorBundle ω ((D × E) [⋀^Fin k]→L[K] F)
      (fun u ↦ (shearBundleCore (K := K) (D := D) (E := E)).Fiber u [⋀^Fin k]→L[K]
        Bundle.Trivial (E →L[K] D) F u)
      𝓘(K, E →L[K] D) :=
  shearBundle_realization k shearBundleCore shearChartWeight (fun _ _ _ ↦ rfl) false true
    rfl rfl (by simp [shearChartWeight]) u₀ hA

end AlternatingAnalytic
