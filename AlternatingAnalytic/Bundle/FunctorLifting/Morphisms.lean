import AlternatingAnalytic.Bundle.FunctorLifting.Cocycle
import AlternatingAnalytic.Bundle.FunctorLifting.Coordinates

/-!
# Lifting bundle morphisms and natural transformations

A tuple of bundle morphisms (reversed in the contravariant variables) has local operator
expressions in the trivializations at each point; applying the functor to them gives the fibers of
the lifted morphism between the glued bundles. In the trivializations at a fixed point `x₀`, the
lifted morphism is `F` applied to the local expressions at `x₀`, so it is `Cⁿ` when `F` preserves
`Cⁿ` families on open subsets of the model space. A natural transformation gives the constant
operator of its component, which intertwines the two transition systems by naturality; it is a
`Cⁿ` morphism with no regularity assumption on the functors beyond the existence of the bundles.
Identities and composition are preserved fiberwise.
-/

noncomputable section

open Bundle Set CategoryTheory Opposite Filter
open scoped Bundle Manifold ContDiff Topology

universe u

namespace AlternatingAnalytic.FunctorLifting

section FiberInstances

variable {K M F ι : Type*} [NontriviallyNormedField K] [TopologicalSpace M]
  [NormedAddCommGroup F] [NormedSpace K F]

/-- The fibers of a vector bundle core are topological groups (they are the model fiber). -/
instance (Z : VectorBundleCore K M F ι) (x : M) : IsTopologicalAddGroup (Z.Fiber x) :=
  inferInstanceAs (IsTopologicalAddGroup F)

/-- Scalar multiplication on the fibers of a vector bundle core is continuous. -/
instance (Z : VectorBundleCore K M F ι) (x : M) : ContinuousSMul K (Z.Fiber x) :=
  inferInstanceAs (ContinuousSMul K F)

end FiberInstances

variable {K : Type u} [NontriviallyNormedField K] {P : Type*} [NormedAddCommGroup P]
  [NormedSpace K P] {M : Type*} [TopologicalSpace M] [ChartedSpace P M] {n : ℕ∞ω} {p q : ℕ}
  {A : Fin p → Type u} [∀ a, NormedAddCommGroup (A a)] [∀ a, NormedSpace K (A a)]
  {EA : Fin p → M → Type u} [∀ a x, TopologicalSpace (EA a x)]
  [∀ a, TopologicalSpace (TotalSpace (A a) (EA a))] [∀ a, FiberBundle (A a) (EA a)]
  [∀ a x, AddCommGroup (EA a x)] [∀ a x, Module K (EA a x)] [∀ a, VectorBundle K (A a) (EA a)]
  {B : Fin q → Type u} [∀ b, NormedAddCommGroup (B b)] [∀ b, NormedSpace K (B b)]
  {EB : Fin q → M → Type u} [∀ b x, TopologicalSpace (EB b x)]
  [∀ b, TopologicalSpace (TotalSpace (B b) (EB b))] [∀ b, FiberBundle (B b) (EB b)]
  [∀ b x, AddCommGroup (EB b x)] [∀ b x, Module K (EB b x)] [∀ b, VectorBundle K (B b) (EB b)]

section Transformations

variable {F G : VarCat K p q ⥤ NormedSpaceCat K}

/-- A natural transformation intertwines the lifted transition functions. -/
theorem inCoordinates_liftApp (η : F ⟶ G) (hV : LiftContinuous A EA B EB F)
    (hV' : LiftContinuous A EA B EB G) {x₀ x : M}
    (hx : x ∈ commonBaseSet A EA B EB x₀) :
    ContinuousLinearMap.inCoordinates (F.obj (modelObj A B)) (liftCore A EA B EB F hV).Fiber
        (G.obj (modelObj A B)) (liftCore A EA B EB G hV').Fiber x₀ x x₀ x
        (η.app (modelObj A B)) =
      η.app (modelObj A B) := by
  rw [VectorBundleCore.inCoordinates_eq _ _ _ hx hx]
  change F.map (homOfCoords (transition A EA B EB x₀ x x)) ≫ η.app (modelObj A B) ≫
      G.map (homOfCoords (transition A EA B EB x x₀ x)) = η.app (modelObj A B)
  rw [← η.naturality, ← Category.assoc, ← F.map_comp,
    homOfCoords_transition_comp ⟨⟨hx, mem_commonBaseSet_self x⟩, hx⟩,
    homOfCoords_transition_self hx, F.map_id, Category.id_comp]

/-- The components of a natural transformation form a `Cⁿ` morphism of the glued bundles. -/
theorem contMDiff_liftApp (η : F ⟶ G) (hV : LiftContinuous A EA B EB F)
    (hV' : LiftContinuous A EA B EB G) :
    ContMDiff 𝓘(K, P) (𝓘(K, P).prod 𝓘(K, F.obj (modelObj A B) →L[K] G.obj (modelObj A B))) n
      (fun x ↦ TotalSpace.mk' (F.obj (modelObj A B) →L[K] G.obj (modelObj A B))
        (E := fun x ↦ (liftCore A EA B EB F hV).Fiber x →L[K] (liftCore A EA B EB G hV').Fiber x)
        x (η.app (modelObj A B))) := by
  intro x₀
  apply (contMDiffAt_hom_bundle _).mpr
  refine ⟨contMDiffAt_id, ?_⟩
  apply (contMDiffAt_const (c := (η.app (modelObj A B) :
    F.obj (modelObj A B) →L[K] G.obj (modelObj A B)))).congr_of_eventuallyEq
  have hU : IsOpen (commonBaseSet A EA B EB x₀) := isOpen_commonBaseSet x₀
  filter_upwards [hU.mem_nhds (mem_commonBaseSet_self x₀)] with x hx
  exact inCoordinates_liftApp η hV hV' hx

end Transformations

section Maps

variable {A' : Fin p → Type u} [∀ a, NormedAddCommGroup (A' a)] [∀ a, NormedSpace K (A' a)]
  {EA' : Fin p → M → Type u} [∀ a x, TopologicalSpace (EA' a x)]
  [∀ a, TopologicalSpace (TotalSpace (A' a) (EA' a))] [∀ a, FiberBundle (A' a) (EA' a)]
  [∀ a x, AddCommGroup (EA' a x)] [∀ a x, Module K (EA' a x)]
  [∀ a, VectorBundle K (A' a) (EA' a)]
  {B' : Fin q → Type u} [∀ b, NormedAddCommGroup (B' b)] [∀ b, NormedSpace K (B' b)]
  {EB' : Fin q → M → Type u} [∀ b x, TopologicalSpace (EB' b x)]
  [∀ b, TopologicalSpace (TotalSpace (B' b) (EB' b))] [∀ b, FiberBundle (B' b) (EB' b)]
  [∀ b x, AddCommGroup (EB' b x)] [∀ b x, Module K (EB' b x)]
  [∀ b, VectorBundle K (B' b) (EB' b)]

/-- The local operator expressions at `x` of a tuple of fiberwise maps, in the trivializations
at `x₀`; the maps go backwards in the contravariant variables. -/
def localTupleAt (ta : ∀ a (x : M), EA' a x →L[K] EA a x) (tb : ∀ b (x : M), EB b x →L[K] EB' b x)
    (x₀ x : M) : HomCoords (modelObj (K := K) A B) (modelObj A' B') :=
  (fun a ↦ ContinuousLinearMap.inCoordinates (A' a) (EA' a) (A a) (EA a) x₀ x x₀ x (ta a x),
    fun b ↦ ContinuousLinearMap.inCoordinates (B b) (EB b) (B' b) (EB' b) x₀ x x₀ x (tb b x))

/-- The local operator expressions at `x` of a tuple of fiberwise maps, in the trivializations
at `x` itself: the fibers of the lifted morphism are `F` applied to them. -/
def localTuple (ta : ∀ a (x : M), EA' a x →L[K] EA a x) (tb : ∀ b (x : M), EB b x →L[K] EB' b x)
    (x : M) : HomCoords (modelObj (K := K) A B) (modelObj A' B') :=
  (fun a ↦ ContinuousLinearMap.inCoordinates (A' a) (EA' a) (A a) (EA a) x x x x (ta a x),
    fun b ↦ ContinuousLinearMap.inCoordinates (B b) (EB b) (B' b) (EB' b) x x x x (tb b x))

/-- Conjugating the local expressions at `x` by the transitions gives those at `x₀`. -/
theorem homOfCoords_localTuple_conj (ta : ∀ a (x : M), EA' a x →L[K] EA a x)
    (tb : ∀ b (x : M), EB b x →L[K] EB' b x) {x₀ x : M}
    (hx : x ∈ commonBaseSet A EA B EB x₀) (hx' : x ∈ commonBaseSet A' EA' B' EB' x₀) :
    homOfCoords (transition (K := K) A EA B EB x₀ x x) ≫
        homOfCoords (localTuple (A := A) (A' := A') (B := B) (B' := B') ta tb x) ≫
        homOfCoords (transition A' EA' B' EB' x x₀ x) =
      homOfCoords (localTupleAt (A := A) (A' := A') (B := B) (B' := B') ta tb x₀ x) := by
  refine Prod.ext (funext fun a ↦ Quiver.Hom.unop_inj ?_) (funext fun b ↦ ?_)
  · exact coordChangeL_comp_inCoordinates_comp (mem_baseSet_left hx' a) (mem_baseSet_left hx a)
      (ta a x)
  · exact (ContinuousLinearMap.comp_assoc _ _ _).trans
      (coordChangeL_comp_inCoordinates_comp (mem_baseSet_right hx b) (mem_baseSet_right hx' b)
        (tb b x))

/-- In the trivializations at `x₀`, the lifted morphism is `F` applied to the local expressions
at `x₀`. -/
theorem inCoordinates_liftHom {F : VarCat K p q ⥤ NormedSpaceCat K}
    (hV : LiftContinuous A EA B EB F) (hV' : LiftContinuous A' EA' B' EB' F)
    (ta : ∀ a (x : M), EA' a x →L[K] EA a x) (tb : ∀ b (x : M), EB b x →L[K] EB' b x)
    {x₀ x : M} (hx : x ∈ commonBaseSet A EA B EB x₀) (hx' : x ∈ commonBaseSet A' EA' B' EB' x₀) :
    ContinuousLinearMap.inCoordinates (F.obj (modelObj A B)) (liftCore A EA B EB F hV).Fiber
        (F.obj (modelObj A' B')) (liftCore A' EA' B' EB' F hV').Fiber x₀ x x₀ x
        (F.map (homOfCoords (localTuple (A := A) (A' := A') (B := B) (B' := B') ta tb x))) =
      F.map (homOfCoords (localTupleAt (A := A) (A' := A') (B := B) (B' := B') ta tb x₀ x)) := by
  rw [VectorBundleCore.inCoordinates_eq _ _ _ hx hx', ← homOfCoords_localTuple_conj ta tb hx hx',
    F.map_comp, F.map_comp]
  rfl

variable [∀ a x, IsTopologicalAddGroup (EA a x)] [∀ a x, ContinuousSMul K (EA a x)]
  [∀ b x, IsTopologicalAddGroup (EB' b x)] [∀ b x, ContinuousSMul K (EB' b x)]
  [∀ a, ContMDiffVectorBundle (𝕜 := K) n (A a) (EA a) 𝓘(K, P)]
  [∀ b, ContMDiffVectorBundle (𝕜 := K) n (B b) (EB b) 𝓘(K, P)]
  [∀ a, ContMDiffVectorBundle (𝕜 := K) n (A' a) (EA' a) 𝓘(K, P)]
  [∀ b, ContMDiffVectorBundle (𝕜 := K) n (B' b) (EB' b) 𝓘(K, P)]

/-- The local expressions at `x₀` of `Cⁿ` morphisms are `Cⁿ` near `x₀`. -/
theorem contMDiffOn_localTupleAt
    (TA : ∀ a, ContMDiffSection 𝓘(K, P) (A' a →L[K] A a) n (fun x ↦ EA' a x →L[K] EA a x))
    (TB : ∀ b, ContMDiffSection 𝓘(K, P) (B b →L[K] B' b) n (fun x ↦ EB b x →L[K] EB' b x))
    (x₀ : M) :
    ContMDiffOn 𝓘(K, P) 𝓘(K, HomCoords (modelObj (K := K) A B) (modelObj A' B')) n
      (localTupleAt (A := A) (A' := A') (B := B) (B' := B') (fun a ↦ ⇑(TA a)) (fun b ↦ ⇑(TB b)) x₀)
      (commonBaseSet A EA B EB x₀ ∩ commonBaseSet A' EA' B' EB' x₀) := by
  have hU : IsOpen (commonBaseSet A EA B EB x₀ ∩ commonBaseSet A' EA' B' EB' x₀) :=
    (isOpen_commonBaseSet x₀).inter (isOpen_commonBaseSet x₀)
  refine ContMDiffOn.prodMk_space (contMDiffOn_pi_space.2 fun a ↦ ?_)
    (contMDiffOn_pi_space.2 fun b ↦ ?_)
  · exact contMDiffOn_inCoordinates_of_section (TA a) x₀ hU fun x hx ↦
      ⟨mem_baseSet_left hx.2 a, mem_baseSet_left hx.1 a⟩
  · exact contMDiffOn_inCoordinates_of_section (TB b) x₀ hU fun x hx ↦
      ⟨mem_baseSet_right hx.1 b, mem_baseSet_right hx.2 b⟩

/-- Under family preservation, the lifted morphism of a tuple of `Cⁿ` morphisms is a `Cⁿ`
section of the Hom bundle between the glued bundles. -/
theorem contMDiff_liftHom [IsManifold 𝓘(K, P) n M] {F : VarCat K p q ⥤ NormedSpaceCat K}
    (hF : PreservesFamilies n P F)
    (hV : LiftContinuous A EA B EB F) (hV' : LiftContinuous A' EA' B' EB' F)
    (TA : ∀ a, ContMDiffSection 𝓘(K, P) (A' a →L[K] A a) n (fun x ↦ EA' a x →L[K] EA a x))
    (TB : ∀ b, ContMDiffSection 𝓘(K, P) (B b →L[K] B' b) n (fun x ↦ EB b x →L[K] EB' b x)) :
    ContMDiff 𝓘(K, P) (𝓘(K, P).prod 𝓘(K, F.obj (modelObj A B) →L[K] F.obj (modelObj A' B'))) n
      (fun x ↦ TotalSpace.mk' (F.obj (modelObj A B) →L[K] F.obj (modelObj A' B'))
        (E := fun x ↦
          (liftCore A EA B EB F hV).Fiber x →L[K] (liftCore A' EA' B' EB' F hV').Fiber x)
        x (F.map (homOfCoords (localTuple (A := A) (A' := A') (B := B) (B' := B')
          (fun a ↦ ⇑(TA a)) (fun b ↦ ⇑(TB b)) x)))) := by
  intro x₀
  apply (contMDiffAt_hom_bundle _).mpr
  refine ⟨contMDiffAt_id, ?_⟩
  have hU : IsOpen (commonBaseSet A EA B EB x₀ ∩ commonBaseSet A' EA' B' EB' x₀) :=
    (isOpen_commonBaseSet x₀).inter (isOpen_commonBaseSet x₀)
  have hx₀ : x₀ ∈ commonBaseSet A EA B EB x₀ ∩ commonBaseSet A' EA' B' EB' x₀ :=
    ⟨mem_commonBaseSet_self x₀, mem_commonBaseSet_self x₀⟩
  have hreg := contMDiffOn_comp_of_preservesFamilies
    (Φ := fun f ↦ (F.map (homOfCoords f) : F.obj (modelObj A B) →L[K] F.obj (modelObj A' B')))
    (hF (modelObj A B) (modelObj A' B')) hU (contMDiffOn_localTupleAt TA TB x₀)
  refine (hreg.contMDiffAt (hU.mem_nhds hx₀)).congr_of_eventuallyEq ?_
  filter_upwards [hU.mem_nhds hx₀] with x hx
  exact inCoordinates_liftHom hV hV' _ _ hx.1 hx.2

end Maps

section Functoriality

variable {A' : Fin p → Type u} [∀ a, NormedAddCommGroup (A' a)] [∀ a, NormedSpace K (A' a)]
  {EA' : Fin p → M → Type u} [∀ a x, TopologicalSpace (EA' a x)]
  [∀ a, TopologicalSpace (TotalSpace (A' a) (EA' a))] [∀ a, FiberBundle (A' a) (EA' a)]
  [∀ a x, AddCommGroup (EA' a x)] [∀ a x, Module K (EA' a x)]
  [∀ a, VectorBundle K (A' a) (EA' a)]
  {B' : Fin q → Type u} [∀ b, NormedAddCommGroup (B' b)] [∀ b, NormedSpace K (B' b)]
  {EB' : Fin q → M → Type u} [∀ b x, TopologicalSpace (EB' b x)]
  [∀ b, TopologicalSpace (TotalSpace (B' b) (EB' b))] [∀ b, FiberBundle (B' b) (EB' b)]
  [∀ b x, AddCommGroup (EB' b x)] [∀ b x, Module K (EB' b x)]
  [∀ b, VectorBundle K (B' b) (EB' b)]
  {A'' : Fin p → Type u} [∀ a, NormedAddCommGroup (A'' a)] [∀ a, NormedSpace K (A'' a)]
  {EA'' : Fin p → M → Type u} [∀ a x, TopologicalSpace (EA'' a x)]
  [∀ a, TopologicalSpace (TotalSpace (A'' a) (EA'' a))] [∀ a, FiberBundle (A'' a) (EA'' a)]
  [∀ a x, AddCommGroup (EA'' a x)] [∀ a x, Module K (EA'' a x)]
  [∀ a, VectorBundle K (A'' a) (EA'' a)]
  {B'' : Fin q → Type u} [∀ b, NormedAddCommGroup (B'' b)] [∀ b, NormedSpace K (B'' b)]
  {EB'' : Fin q → M → Type u} [∀ b x, TopologicalSpace (EB'' b x)]
  [∀ b, TopologicalSpace (TotalSpace (B'' b) (EB'' b))] [∀ b, FiberBundle (B'' b) (EB'' b)]
  [∀ b x, AddCommGroup (EB'' b x)] [∀ b x, Module K (EB'' b x)]
  [∀ b, VectorBundle K (B'' b) (EB'' b)]

/-- The local expressions of identity maps give the identity of `C^ε`. -/
theorem homOfCoords_localTuple_id (x : M) :
    homOfCoords (localTuple (A' := A) (EA' := EA) (B' := B) (EB' := EB)
      (fun a x ↦ ContinuousLinearMap.id K (EA a x)) (fun b x ↦ ContinuousLinearMap.id K (EB b x))
      x) = 𝟙 (modelObj (K := K) A B) := by
  refine Prod.ext (funext fun a ↦ Quiver.Hom.unop_inj ?_) (funext fun b ↦ ?_)
  · exact inCoordinates_self_id x
  · exact inCoordinates_self_id x

/-- The local expressions of composites compose in `C^ε`, reversed in the contravariant
variables. -/
theorem homOfCoords_localTuple_comp (ta : ∀ a (x : M), EA' a x →L[K] EA a x)
    (tb : ∀ b (x : M), EB b x →L[K] EB' b x) (ta' : ∀ a (x : M), EA'' a x →L[K] EA' a x)
    (tb' : ∀ b (x : M), EB' b x →L[K] EB'' b x) (x : M) :
    homOfCoords (localTuple (K := K) (A := A) (A' := A'') (B := B) (B' := B'')
        (fun a x ↦ (ta a x).comp (ta' a x)) (fun b x ↦ (tb' b x).comp (tb b x)) x) =
      homOfCoords (localTuple (A := A) (A' := A') (B := B) (B' := B') ta tb x) ≫
        homOfCoords (localTuple (A := A') (A' := A'') (B := B') (B' := B'') ta' tb' x) := by
  refine Prod.ext (funext fun a ↦ Quiver.Hom.unop_inj ?_) (funext fun b ↦ ?_)
  · exact inCoordinates_self_comp x (ta' a x) (ta a x)
  · exact inCoordinates_self_comp x (tb b x) (tb' b x)

end Functoriality

end AlternatingAnalytic.FunctorLifting
