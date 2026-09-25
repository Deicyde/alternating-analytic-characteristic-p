import AlternatingAnalytic.Geometry.FiniteCoordinateManifoldFamilies
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Topology.VectorBundle.ContinuousAlternatingMap

/-!
# Analytic alternating bundles over finite-coordinate manifolds

The existing topological bundle of continuous alternating maps is `C^n` whenever
the joint model action preserves `C^n` families on open subsets of the fixed base.
For analytic manifolds with supplied continuous linear coordinates in `K^d`,
finite-coordinate family preservation discharges this premise for every degree.

These results use Mathlib's existing total-space topology and its actual,
topological fibers. They formalize the object construction and transition formula
of `paper/charp.tex`, `fam:thm:finite-bundles` and `fam:eq:bundle-transitions`.
The morphism and category-theoretic bifunctor constructions are separate.
-/

noncomputable section

open Bundle Set
open scoped Bundle Manifold ContDiff

namespace AlternatingAnalytic

variable {K M F₁ F₂ : Type*} [NontriviallyNormedField K] [TopologicalSpace M]
  [NormedAddCommGroup F₁] [NormedSpace K F₁]
  [NormedAddCommGroup F₂] [NormedSpace K F₂]
  {E₁ E₂ : M → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module K (E₁ x)]
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module K (E₂ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [TopologicalSpace (TotalSpace F₂ E₂)]

section Transitions

variable (k : ℕ)
  (e₁ e₁' : Trivialization F₁ (π F₁ E₁))
  (e₂ e₂' : Trivialization F₂ (π F₂ E₂))
  [e₁.IsLinear K] [e₁'.IsLinear K] [e₂.IsLinear K] [e₂'.IsLinear K]

/-- The alternating transition uses the reverse source transition and the forward
target transition. This algebraic identity is independent of regularity order. -/
theorem continuousAlternatingMapCoordChange_eq_alternatingMapAction (b : M) :
    Pretrivialization.continuousAlternatingMapCoordChange K (Fin k) e₁ e₁' e₂ e₂' b =
      alternatingMapAction k
        ((e₁'.coordChangeL K e₁ b : F₁ →L[K] F₁),
          (e₂.coordChangeL K e₂' b : F₂ →L[K] F₂)) := by
  simp only [Pretrivialization.continuousAlternatingMapCoordChange,
    ContinuousLinearEquiv.coe_continuousAlternatingMapCongr,
    ContinuousLinearEquiv.symm_symm, alternatingMapAction]

variable [∀ x, TopologicalSpace (E₁ x)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₁ E₁] [FiberBundle F₂ E₂]

/-- On the common domain, the model action is the actual pretrivialization change. -/
theorem alternatingMapAction_coordChange_apply (b : M)
    (hb : b ∈ e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet))
    (L : F₁ [⋀^Fin k]→L[K] F₂) :
    alternatingMapAction k
        ((e₁'.coordChangeL K e₁ b : F₁ →L[K] F₁),
          (e₂.coordChangeL K e₂' b : F₂ →L[K] F₂)) L =
      (Pretrivialization.continuousAlternatingMap K (Fin k) e₁' e₂'
        ⟨b, (Pretrivialization.continuousAlternatingMap K (Fin k) e₁ e₂).symm b L⟩).2 := by
  rw [← continuousAlternatingMapCoordChange_eq_alternatingMapAction]
  exact Pretrivialization.continuousAlternatingMapCoordChange_apply b hb L

end Transitions

variable [∀ x, TopologicalSpace (E₁ x)] [∀ x, TopologicalSpace (E₂ x)]
  [FiberBundle F₁ E₁] [VectorBundle K F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle K F₂ E₂]

section Assembly

variable {P H : Type*} [NormedAddCommGroup P] [NormedSpace K P]
  [TopologicalSpace H] [ChartedSpace H M] {I : ModelWithCorners K P H} {n : ℕ∞ω}
  [ContMDiffVectorBundle n F₁ E₁ I] [ContMDiffVectorBundle n F₂ E₂ I]
  (k : ℕ)
  (hfamily : ∀ {U : Set M}, IsOpen U →
    ∀ {γ : M → (F₁ →L[K] F₁) × (F₂ →L[K] F₂)},
      ContMDiffOn I 𝓘(K, (F₁ →L[K] F₁) × (F₂ →L[K] F₂)) n γ U →
      ContMDiffOn I 𝓘(K, (F₁ [⋀^Fin k]→L[K] F₂) →L[K] (F₁ [⋀^Fin k]→L[K] F₂))
        n (alternatingMapAction k ∘ γ) U)

include hfamily

/-- Local family preservation makes the alternating transition operators `C^n`
on the four-way open overlap. No global regularity of the joint action is assumed. -/
theorem contMDiffOn_continuousAlternatingMapCoordChange_of_family
    (e₁ e₁' : Trivialization F₁ (π F₁ E₁))
    (e₂ e₂' : Trivialization F₂ (π F₂ E₂))
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁']
    [MemTrivializationAtlas e₂] [MemTrivializationAtlas e₂'] :
    ContMDiffOn I 𝓘(K, (F₁ [⋀^Fin k]→L[K] F₂) →L[K] (F₁ [⋀^Fin k]→L[K] F₂)) n
      (Pretrivialization.continuousAlternatingMapCoordChange K (Fin k) e₁ e₁' e₂ e₂')
      (e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) := by
  have h₁ := contMDiffOn_coordChangeL (IB := I) (n := n) e₁' e₁
  have h₂ := contMDiffOn_coordChangeL (IB := I) (n := n) e₂ e₂'
  have hpair := (h₁.mono (show
      e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet) ⊆
        e₁'.baseSet ∩ e₁.baseSet from fun _ h ↦ ⟨h.2.1, h.1.1⟩)).prodMk_space
    (h₂.mono (fun _ h ↦ ⟨h.1.2, h.2.2⟩))
  have h := hfamily
    ((e₁.open_baseSet.inter e₂.open_baseSet).inter
      (e₁'.open_baseSet.inter e₂'.open_baseSet)) hpair
  exact h.congr fun b _ ↦
    continuousAlternatingMapCoordChange_eq_alternatingMapAction k e₁ e₁' e₂ e₂' b

variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul K (E₂ x)]

/-- Assemble regularity on the existing alternating prebundle, at any order and
over an arbitrary model with corners, from local joint-action family preservation. -/
theorem alternatingVectorPrebundle_isContMDiff_of_family :
    (Bundle.ContinuousAlternatingMap.vectorPrebundle K (Fin k) F₁ E₁ F₂ E₂).IsContMDiff
      I n where
  exists_contMDiffCoordChange := by
    rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩
    exact ⟨Pretrivialization.continuousAlternatingMapCoordChange K (Fin k) e₁ e₁' e₂ e₂',
      contMDiffOn_continuousAlternatingMapCoordChange_of_family k hfamily e₁ e₁' e₂ e₂',
      Pretrivialization.continuousAlternatingMapCoordChange_apply⟩

/-- The actual alternating bundle, with Mathlib's existing topology and fibers,
is `C^n` under local family preservation. -/
theorem contMDiffVectorBundle_alternating_of_family :
    ContMDiffVectorBundle n (F₁ [⋀^Fin k]→L[K] F₂)
      (fun x ↦ E₁ x [⋀^Fin k]→L[K] E₂ x) I := by
  let := alternatingVectorPrebundle_isContMDiff_of_family (E₁ := E₁) (E₂ := E₂) k hfamily
  exact VectorPrebundle.contMDiffVectorBundle I
    (Bundle.ContinuousAlternatingMap.vectorPrebundle K (Fin k) F₁ E₁ F₂ E₂)

end Assembly

section BundleTransitions

variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul K (E₂ x)]

/-- The actual alternating-bundle coordinate operator is the joint model action
on the reverse/forward transition pair on every common trivializing domain. -/
theorem coordChangeL_continuousAlternatingMap_eq_alternatingMapAction (k : ℕ)
    (e₁ e₁' : Trivialization F₁ (π F₁ E₁))
    (e₂ e₂' : Trivialization F₂ (π F₂ E₂))
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁']
    [MemTrivializationAtlas e₂] [MemTrivializationAtlas e₂'] (b : M)
    (hb : b ∈ e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) :
    ((e₁.continuousAlternatingMap K (Fin k) e₂).coordChangeL K
        (e₁'.continuousAlternatingMap K (Fin k) e₂') b :
        (F₁ [⋀^Fin k]→L[K] F₂) →L[K] (F₁ [⋀^Fin k]→L[K] F₂)) =
      alternatingMapAction k
        ((e₁'.coordChangeL K e₁ b : F₁ →L[K] F₁),
          (e₂.coordChangeL K e₂' b : F₂ →L[K] F₂)) := by
  ext L v
  change (e₁.continuousAlternatingMap K (Fin k) e₂).coordChangeL K
      (e₁'.continuousAlternatingMap K (Fin k) e₂') b L v = _
  rw [Trivialization.coordChangeL_apply _ _ hb]
  exact congrArg (fun m ↦ m v)
    (alternatingMapAction_coordChange_apply k e₁ e₁' e₂ e₂' b hb L).symm

end BundleTransitions

section FiniteCoordinates

variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul K (E₂ x)]

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace K P]
  [ChartedSpace P M] [IsManifold 𝓘(K, P) ω M]
  [ContMDiffVectorBundle ω F₁ E₁ 𝓘(K, P)]
  [ContMDiffVectorBundle ω F₂ E₂ 𝓘(K, P)]
  {d : ℕ} (c : P ≃L[K] (Fin d → K)) (k : ℕ)

include c

/-- Every alternating degree gives an analytic prebundle over a finite-coordinate
analytic base. The field and model fibers need not be complete. -/
theorem alternatingVectorPrebundle_isContMDiff_of_finiteCoordinates :
    (Bundle.ContinuousAlternatingMap.vectorPrebundle K (Fin k) F₁ E₁ F₂ E₂).IsContMDiff
      𝓘(K, P) ω :=
  alternatingVectorPrebundle_isContMDiff_of_family k
    (fun {_} hU {_} hγ ↦ contMDiffOn_alternatingMapAction_of_finiteCoordinates c k hU hγ)

/-- Analytic object closure on the existing alternating bundle, with the supplied
finite coordinates as an explicit argument. Both `d = 0` and `k = 0` are included. -/
theorem contMDiffVectorBundle_alternating_of_finiteCoordinates :
    ContMDiffVectorBundle ω (F₁ [⋀^Fin k]→L[K] F₂)
      (fun x ↦ E₁ x [⋀^Fin k]→L[K] E₂ x) 𝓘(K, P) :=
  contMDiffVectorBundle_alternating_of_family k
    (fun {_} hU {_} hγ ↦ contMDiffOn_alternatingMapAction_of_finiteCoordinates c k hU hγ)

/-- The finite-coordinate analytic alternating-bundle theorem: the existing
prebundle is analytic, its actual bundle is analytic, and both the model and actual
transition operators have the prescribed contravariant/covariant formula. -/
theorem analyticAlternatingBundle_of_finiteCoordinates :
    (Bundle.ContinuousAlternatingMap.vectorPrebundle K (Fin k) F₁ E₁ F₂ E₂).IsContMDiff
        𝓘(K, P) ω ∧
      ContMDiffVectorBundle ω (F₁ [⋀^Fin k]→L[K] F₂)
        (fun x ↦ E₁ x [⋀^Fin k]→L[K] E₂ x) 𝓘(K, P) ∧
      ∀ (e₁ e₁' : Trivialization F₁ (π F₁ E₁))
        (e₂ e₂' : Trivialization F₂ (π F₂ E₂))
        [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁']
        [MemTrivializationAtlas e₂] [MemTrivializationAtlas e₂'],
        (∀ b, Pretrivialization.continuousAlternatingMapCoordChange
            K (Fin k) e₁ e₁' e₂ e₂' b =
          alternatingMapAction k
            ((e₁'.coordChangeL K e₁ b : F₁ →L[K] F₁),
              (e₂.coordChangeL K e₂' b : F₂ →L[K] F₂))) ∧
        ∀ b ∈ e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet),
          ((e₁.continuousAlternatingMap K (Fin k) e₂).coordChangeL K
              (e₁'.continuousAlternatingMap K (Fin k) e₂') b :
              (F₁ [⋀^Fin k]→L[K] F₂) →L[K] (F₁ [⋀^Fin k]→L[K] F₂)) =
            alternatingMapAction k
              ((e₁'.coordChangeL K e₁ b : F₁ →L[K] F₁),
                (e₂.coordChangeL K e₂' b : F₂ →L[K] F₂)) := by
  refine ⟨alternatingVectorPrebundle_isContMDiff_of_finiteCoordinates c k,
    contMDiffVectorBundle_alternating_of_finiteCoordinates c k, ?_⟩
  intro e₁ e₁' e₂ e₂' _ _ _ _
  exact ⟨continuousAlternatingMapCoordChange_eq_alternatingMapAction k e₁ e₁' e₂ e₂',
    coordChangeL_continuousAlternatingMap_eq_alternatingMapAction k e₁ e₁' e₂ e₂'⟩

end FiniteCoordinates

end AlternatingAnalytic
