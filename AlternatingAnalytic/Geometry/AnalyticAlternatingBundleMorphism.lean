import AlternatingAnalytic.Geometry.AlternatingBundleMorphismAlgebra
import AlternatingAnalytic.Geometry.ContMDiffBundleHom

/-!
# Operator regularity of alternating bundle morphisms

The fiberwise action uses only topological continuous linear maps. Its model
coordinates are the four-model alternating action. Local preservation of regular
operator families assembles a genuine Hom section at arbitrary order and over
an arbitrary model with corners. On finite-coordinate analytic manifolds the
preservation premise and both endpoint instances are discharged unconditionally.
-/

noncomputable section

open Bundle Set
open scoped Bundle Manifold ContDiff

namespace AlternatingAnalytic

variable {K M A A' B B' : Type*} [NontriviallyNormedField K] [TopologicalSpace M]
  [NormedAddCommGroup A] [NormedSpace K A]
  [NormedAddCommGroup A'] [NormedSpace K A']
  [NormedAddCommGroup B] [NormedSpace K B]
  [NormedAddCommGroup B'] [NormedSpace K B']
  {E E' F F' : M → Type*}
  [∀ b, AddCommGroup (E b)] [∀ b, Module K (E b)] [∀ b, TopologicalSpace (E b)]
  [∀ b, AddCommGroup (E' b)] [∀ b, Module K (E' b)] [∀ b, TopologicalSpace (E' b)]
  [∀ b, AddCommGroup (F b)] [∀ b, Module K (F b)] [∀ b, TopologicalSpace (F b)]
  [∀ b, AddCommGroup (F' b)] [∀ b, Module K (F' b)] [∀ b, TopologicalSpace (F' b)]
  [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousSMul K (E b)]
  [∀ b, IsTopologicalAddGroup (F b)] [∀ b, ContinuousSMul K (F b)]
  [∀ b, IsTopologicalAddGroup (F' b)] [∀ b, ContinuousSMul K (F' b)]
  [TopologicalSpace (TotalSpace A E)] [TopologicalSpace (TotalSpace A' E')]
  [TopologicalSpace (TotalSpace B F)] [TopologicalSpace (TotalSpace B' F')]
  [FiberBundle A E] [VectorBundle K A E]
  [FiberBundle A' E'] [VectorBundle K A' E']
  [FiberBundle B F] [VectorBundle K B F]
  [FiberBundle B' F'] [VectorBundle K B' F']

section Regularity

variable {P H : Type*} [NormedAddCommGroup P] [NormedSpace K P]
  [TopologicalSpace H] [ChartedSpace H M] {I : ModelWithCorners K P H} {n : ℕ∞ω}
  [ContMDiffVectorBundle n A E I] [ContMDiffVectorBundle n A' E' I]
  [ContMDiffVectorBundle n B F I] [ContMDiffVectorBundle n B' F' I]
  (k : ℕ)
  (hfamily : ∀ {U : Set M}, IsOpen U →
    ∀ {γ : M → (A' →L[K] A) × (B →L[K] B')},
      ContMDiffOn I 𝓘(K, (A' →L[K] A) × (B →L[K] B')) n γ U →
      ContMDiffOn I 𝓘(K, (A [⋀^Fin k]→L[K] B) →L[K] (A' [⋀^Fin k]→L[K] B'))
        n (alternatingMapAction k ∘ γ) U)
  (u : ContMDiffSection I (A' →L[K] A) n (fun b ↦ E' b →L[K] E b))
  (v : ContMDiffSection I (B →L[K] B') n (fun b ↦ F b →L[K] F' b))

include hfamily

/-- Operator coordinates are regular in every pair of input atlas charts, on
any open subset of their common valid domain. -/
theorem contMDiffOn_alternatingBundleMap_coordinates_of_family
    (eA : Trivialization A (π A E)) (eA' : Trivialization A' (π A' E'))
    (eB : Trivialization B (π B F)) (eB' : Trivialization B' (π B' F'))
    [MemTrivializationAtlas eA] [MemTrivializationAtlas eA']
    [MemTrivializationAtlas eB] [MemTrivializationAtlas eB']
    {U : Set M} (hU : IsOpen U)
    (hUe : U ⊆ (eA.baseSet ∩ eB.baseSet) ∩ (eA'.baseSet ∩ eB'.baseSet)) :
    ContMDiffOn I 𝓘(K, (A [⋀^Fin k]→L[K] B) →L[K] (A' [⋀^Fin k]→L[K] B')) n
      (fun b ↦ (((eA.continuousAlternatingMap K (Fin k) eB).continuousLinearMap
        (RingHom.id K) (eA'.continuousAlternatingMap K (Fin k) eB'))
          ⟨b, alternatingBundleMap k (u b) (v b)⟩).2) U := by
  have hu := ((eA'.continuousLinearMap (RingHom.id K) eA).contMDiffOn_section_iff
    (IB := I) (n := n) hU (fun b hb ↦ ⟨(hUe hb).2.1, (hUe hb).1.1⟩)).mp
    u.contMDiff.contMDiffOn
  have hv := ((eB.continuousLinearMap (RingHom.id K) eB').contMDiffOn_section_iff
    (IB := I) (n := n) hU (fun b hb ↦ ⟨(hUe hb).1.2, (hUe hb).2.2⟩)).mp
    v.contMDiff.contMDiffOn
  exact (hfamily hU (hu.prodMk_space hv)).congr fun b hb ↦
    alternatingBundleMap_coordinates k eA eA' eB eB' b (hUe hb) (u b) (v b)

variable
  [ContMDiffVectorBundle n (A [⋀^Fin k]→L[K] B)
    (fun b ↦ E b [⋀^Fin k]→L[K] F b) I]
  [ContMDiffVectorBundle n (A' [⋀^Fin k]→L[K] B')
    (fun b ↦ E' b [⋀^Fin k]→L[K] F' b) I]

/-- Local four-model family preservation constructs the actual regular section
of the alternating Hom bundle. Endpoint regularity is an explicit premise. -/
def alternatingBundleHom_of_family :
    ContMDiffSection I ((A [⋀^Fin k]→L[K] B) →L[K] (A' [⋀^Fin k]→L[K] B')) n
      (fun b ↦ (E b [⋀^Fin k]→L[K] F b) →L[K] (E' b [⋀^Fin k]→L[K] F' b)) where
  toFun b := alternatingBundleMap k (u b) (v b)
  contMDiff_toFun := by
    intro b
    let eA := trivializationAt A E b
    let eA' := trivializationAt A' E' b
    let eB := trivializationAt B F b
    let eB' := trivializationAt B' F' b
    let U := (eA.baseSet ∩ eB.baseSet) ∩ (eA'.baseSet ∩ eB'.baseSet)
    have hU : IsOpen U := (eA.open_baseSet.inter eB.open_baseSet).inter
      (eA'.open_baseSet.inter eB'.open_baseSet)
    have hb : b ∈ U :=
      ⟨⟨mem_baseSet_trivializationAt A E b, mem_baseSet_trivializationAt B F b⟩,
        ⟨mem_baseSet_trivializationAt A' E' b, mem_baseSet_trivializationAt B' F' b⟩⟩
    have hcoords := contMDiffOn_alternatingBundleMap_coordinates_of_family
      k hfamily u v eA eA' eB eB' hU subset_rfl
    exact ((eA.continuousAlternatingMap K (Fin k) eB).continuousLinearMap
      (RingHom.id K) (eA'.continuousAlternatingMap K (Fin k) eB')).contMDiffAt_section_iff
      hb |>.mpr (hcoords.contMDiffAt (hU.mem_nhds hb))

@[simp]
theorem alternatingBundleHom_of_family_apply (b : M) :
    alternatingBundleHom_of_family k hfamily u v b = alternatingBundleMap k (u b) (v b) :=
  rfl

/-- The constructed section has the literal postcomposition/pullback value. -/
theorem alternatingBundleHom_of_family_apply_apply (b : M)
    (m : E b [⋀^Fin k]→L[K] F b) :
    alternatingBundleHom_of_family k hfamily u v b m =
      (v b).compContinuousAlternatingMap (m.compContinuousLinearMap (u b)) :=
  rfl

/-- The generic regular section has the exact joint-action operator coordinates
in every choice of atlas trivializations, on their common valid domain. -/
theorem alternatingBundleHom_of_family_coordinates
    (eA : Trivialization A (π A E)) (eA' : Trivialization A' (π A' E'))
    (eB : Trivialization B (π B F)) (eB' : Trivialization B' (π B' F'))
    [MemTrivializationAtlas eA] [MemTrivializationAtlas eA']
    [MemTrivializationAtlas eB] [MemTrivializationAtlas eB']
    (b : M) (hb : b ∈ (eA.baseSet ∩ eB.baseSet) ∩ (eA'.baseSet ∩ eB'.baseSet)) :
    (((eA.continuousAlternatingMap K (Fin k) eB).continuousLinearMap
      (RingHom.id K) (eA'.continuousAlternatingMap K (Fin k) eB'))
        ⟨b, alternatingBundleHom_of_family k hfamily u v b⟩).2 =
      alternatingMapAction k
        (((eA'.continuousLinearMap (RingHom.id K) eA) ⟨b, u b⟩).2,
          ((eB.continuousLinearMap (RingHom.id K) eB') ⟨b, v b⟩).2) :=
  alternatingBundleMap_coordinates k eA eA' eB eB' b hb (u b) (v b)

end Regularity

section FiniteCoordinates

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace K P]
  [ChartedSpace P M] [IsManifold 𝓘(K, P) ω M]
  [ContMDiffVectorBundle ω A E 𝓘(K, P)] [ContMDiffVectorBundle ω A' E' 𝓘(K, P)]
  [ContMDiffVectorBundle ω B F 𝓘(K, P)] [ContMDiffVectorBundle ω B' F' 𝓘(K, P)]
  {d : ℕ} (c : P ≃L[K] (Fin d → K)) (k : ℕ)
  (u : ContMDiffSection 𝓘(K, P) (A' →L[K] A) ω (fun b ↦ E' b →L[K] E b))
  (v : ContMDiffSection 𝓘(K, P) (B →L[K] B') ω (fun b ↦ F b →L[K] F' b))

include c

/-- Unconditional analytic morphism preservation over finite-coordinate open-chart
manifolds, for all degrees and arbitrary normable fibers. -/
def alternatingBundleHom_of_finiteCoordinates :
    ContMDiffSection 𝓘(K, P)
      ((A [⋀^Fin k]→L[K] B) →L[K] (A' [⋀^Fin k]→L[K] B')) ω
      (fun b ↦ (E b [⋀^Fin k]→L[K] F b) →L[K] (E' b [⋀^Fin k]→L[K] F' b)) := by
  letI := contMDiffVectorBundle_alternating_of_finiteCoordinates
    (F₁ := A) (E₁ := E) (F₂ := B) (E₂ := F) c k
  letI := contMDiffVectorBundle_alternating_of_finiteCoordinates
    (F₁ := A') (E₁ := E') (F₂ := B') (E₂ := F') c k
  exact alternatingBundleHom_of_family k
    (fun {_} hU {_} hγ ↦ contMDiffOn_alternatingMapAction_of_finiteCoordinates c k hU hγ) u v

@[simp]
theorem alternatingBundleHom_of_finiteCoordinates_apply (b : M) :
    alternatingBundleHom_of_finiteCoordinates c k u v b =
      alternatingBundleMap k (u b) (v b) :=
  rfl

/-- The analytic section acts by postcomposition and simultaneous pullback
on the actual fibers. -/
theorem alternatingBundleHom_of_finiteCoordinates_apply_apply (b : M)
    (m : E b [⋀^Fin k]→L[K] F b) :
    alternatingBundleHom_of_finiteCoordinates c k u v b m =
      (v b).compContinuousAlternatingMap (m.compContinuousLinearMap (u b)) :=
  rfl

/-- Exact operator coordinates in arbitrary analytic-atlas trivializations. -/
theorem alternatingBundleHom_of_finiteCoordinates_coordinates
    (eA : Trivialization A (π A E)) (eA' : Trivialization A' (π A' E'))
    (eB : Trivialization B (π B F)) (eB' : Trivialization B' (π B' F'))
    [MemTrivializationAtlas eA] [MemTrivializationAtlas eA']
    [MemTrivializationAtlas eB] [MemTrivializationAtlas eB']
    (b : M) (hb : b ∈ (eA.baseSet ∩ eB.baseSet) ∩ (eA'.baseSet ∩ eB'.baseSet)) :
    (((eA.continuousAlternatingMap K (Fin k) eB).continuousLinearMap
      (RingHom.id K) (eA'.continuousAlternatingMap K (Fin k) eB'))
        ⟨b, alternatingBundleHom_of_finiteCoordinates c k u v b⟩).2 =
      alternatingMapAction k
        (((eA'.continuousLinearMap (RingHom.id K) eA) ⟨b, u b⟩).2,
          ((eB.continuousLinearMap (RingHom.id K) eB') ⟨b, v b⟩).2) :=
  alternatingBundleMap_coordinates k eA eA' eB eB' b hb (u b) (v b)

/-- Operator-coordinate analyticity holds on each valid open chart intersection. -/
theorem contMDiffOn_alternatingBundleHom_of_finiteCoordinates_coordinates
    (eA : Trivialization A (π A E)) (eA' : Trivialization A' (π A' E'))
    (eB : Trivialization B (π B F)) (eB' : Trivialization B' (π B' F'))
    [MemTrivializationAtlas eA] [MemTrivializationAtlas eA']
    [MemTrivializationAtlas eB] [MemTrivializationAtlas eB'] :
    ContMDiffOn 𝓘(K, P)
      𝓘(K, (A [⋀^Fin k]→L[K] B) →L[K] (A' [⋀^Fin k]→L[K] B')) ω
      (fun b ↦ (((eA.continuousAlternatingMap K (Fin k) eB).continuousLinearMap
        (RingHom.id K) (eA'.continuousAlternatingMap K (Fin k) eB'))
          ⟨b, alternatingBundleHom_of_finiteCoordinates c k u v b⟩).2)
      ((eA.baseSet ∩ eB.baseSet) ∩ (eA'.baseSet ∩ eB'.baseSet)) :=
  contMDiffOn_alternatingBundleMap_coordinates_of_family k
    (fun {_} hU {_} hγ ↦ contMDiffOn_alternatingMapAction_of_finiteCoordinates c k hU hγ)
    u v eA eA' eB eB'
    ((eA.open_baseSet.inter eB.open_baseSet).inter (eA'.open_baseSet.inter eB'.open_baseSet))
    subset_rfl

/-- Identity is preserved as equality of actual analytic Hom sections. -/
@[simp]
theorem alternatingBundleHom_of_finiteCoordinates_id :
    alternatingBundleHom_of_finiteCoordinates c k
      (contMDiffHomId (I := 𝓘(K, P)) (n := ω) A E)
      (contMDiffHomId (I := 𝓘(K, P)) (n := ω) B F) =
    contMDiffHomId (I := 𝓘(K, P)) (n := ω) (A [⋀^Fin k]→L[K] B)
      (fun b ↦ E b [⋀^Fin k]→L[K] F b) := by
  apply ContMDiffSection.ext
  intro b
  exact alternatingBundleMap_id k

variable {A'' B'' : Type*}
  [NormedAddCommGroup A''] [NormedSpace K A'']
  [NormedAddCommGroup B''] [NormedSpace K B'']
  {E'' F'' : M → Type*}
  [∀ b, AddCommGroup (E'' b)] [∀ b, Module K (E'' b)]
  [∀ b, TopologicalSpace (E'' b)]
  [∀ b, AddCommGroup (F'' b)] [∀ b, Module K (F'' b)]
  [∀ b, TopologicalSpace (F'' b)]
  [∀ b, IsTopologicalAddGroup (F'' b)] [∀ b, ContinuousSMul K (F'' b)]
  [TopologicalSpace (TotalSpace A'' E'')] [TopologicalSpace (TotalSpace B'' F'')]
  [FiberBundle A'' E''] [VectorBundle K A'' E'']
  [FiberBundle B'' F''] [VectorBundle K B'' F'']
  [ContMDiffVectorBundle ω A'' E'' 𝓘(K, P)]
  [ContMDiffVectorBundle ω B'' F'' 𝓘(K, P)]
  [∀ b, IsTopologicalAddGroup (E' b)] [∀ b, ContinuousSMul K (E' b)]
  (u' : ContMDiffSection 𝓘(K, P) (A'' →L[K] A') ω (fun b ↦ E'' b →L[K] E' b))
  (v' : ContMDiffSection 𝓘(K, P) (B' →L[K] B'') ω (fun b ↦ F' b →L[K] F'' b))

/-- Composition reverses the source slot and preserves the target slot, as an
identity of analytic operator Hom sections. -/
theorem alternatingBundleHom_of_finiteCoordinates_comp :
    alternatingBundleHom_of_finiteCoordinates c k
      (contMDiffHomComp u' u) (contMDiffHomComp v v') =
    contMDiffHomComp (alternatingBundleHom_of_finiteCoordinates c k u v)
      (alternatingBundleHom_of_finiteCoordinates c k u' v') := by
  apply ContMDiffSection.ext
  intro b
  exact alternatingBundleMap_comp k (u b) (u' b) (v b) (v' b)

/-- The source theorem with its fiber formula, exact coordinates, and identity
and mixed-variance composition laws. All sections in the conclusion are actual
operator-valued analytic Hom sections. The two further bundles only express the
composition law; the morphism construction itself takes the original four. -/
theorem analyticAlternatingBundleMorphism_of_finiteCoordinates :
    ∃ T : ContMDiffSection 𝓘(K, P)
        ((A [⋀^Fin k]→L[K] B) →L[K] (A' [⋀^Fin k]→L[K] B')) ω
        (fun b ↦ (E b [⋀^Fin k]→L[K] F b) →L[K] (E' b [⋀^Fin k]→L[K] F' b)),
      (∀ b (m : E b [⋀^Fin k]→L[K] F b),
        T b m = (v b).compContinuousAlternatingMap (m.compContinuousLinearMap (u b))) ∧
      (∀ (eA : Trivialization A (π A E)) (eA' : Trivialization A' (π A' E'))
        (eB : Trivialization B (π B F)) (eB' : Trivialization B' (π B' F'))
        [MemTrivializationAtlas eA] [MemTrivializationAtlas eA']
        [MemTrivializationAtlas eB] [MemTrivializationAtlas eB'],
        ∀ b ∈ (eA.baseSet ∩ eB.baseSet) ∩ (eA'.baseSet ∩ eB'.baseSet),
          (((eA.continuousAlternatingMap K (Fin k) eB).continuousLinearMap
            (RingHom.id K) (eA'.continuousAlternatingMap K (Fin k) eB')) ⟨b, T b⟩).2 =
          alternatingMapAction k
            (((eA'.continuousLinearMap (RingHom.id K) eA) ⟨b, u b⟩).2,
              ((eB.continuousLinearMap (RingHom.id K) eB') ⟨b, v b⟩).2)) ∧
      alternatingBundleHom_of_finiteCoordinates c k
        (contMDiffHomId (I := 𝓘(K, P)) (n := ω) A E)
        (contMDiffHomId (I := 𝓘(K, P)) (n := ω) B F) =
        contMDiffHomId (I := 𝓘(K, P)) (n := ω) (A [⋀^Fin k]→L[K] B)
          (fun b ↦ E b [⋀^Fin k]→L[K] F b) ∧
      alternatingBundleHom_of_finiteCoordinates c k
        (contMDiffHomComp u' u) (contMDiffHomComp v v') =
        contMDiffHomComp T (alternatingBundleHom_of_finiteCoordinates c k u' v') := by
  refine ⟨alternatingBundleHom_of_finiteCoordinates c k u v, ?_, ?_, ?_, ?_⟩
  · intro b m
    rfl
  · intro eA eA' eB eB' _ _ _ _ b hb
    exact alternatingBundleHom_of_finiteCoordinates_coordinates c k u v eA eA' eB eB' b hb
  · exact alternatingBundleHom_of_finiteCoordinates_id c k
  · exact alternatingBundleHom_of_finiteCoordinates_comp c k u v u' v'

end FiniteCoordinates

end AlternatingAnalytic
