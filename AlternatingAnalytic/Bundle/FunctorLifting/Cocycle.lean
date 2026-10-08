import AlternatingAnalytic.Bundle.FunctorLifting.ChartFamilies
import AlternatingAnalytic.Category.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.CategoryTheory.Pi.Basic

/-!
# Lifting a mixed-variance functor to transition cocycles

`C^ε = (Vec_Kᵒᵖ)^p × Vec_K^q` is the category of `p` contravariant and `q` covariant normed-space
variables; its hom spaces have operator coordinates `HomCoords X Y` with the maximum norm. A
functor `F : C^ε ⥤ Vec_K` is applied to the transition cocycles of `p + q` vector bundles over a
common trivializing cover indexed by the points of the base: in a contravariant variable the
reverse transition is used. Functoriality gives the cocycle identities, so the result is a
`VectorBundleCore`, and it is `Cⁿ` as soon as `F` preserves `Cⁿ` families parametrized by open
subsets of the model space. The bundles are unbundled families of Mathlib vector bundles.
-/

noncomputable section

open Bundle Set CategoryTheory Opposite
open scoped Bundle Manifold ContDiff

universe u

namespace AlternatingAnalytic.FunctorLifting

section Functors

/-- `C^ε` with `p` contravariant and `q` covariant variables: `(Vec_Kᵒᵖ)^p × Vec_K^q`. -/
abbrev VarCat (K : Type u) [NontriviallyNormedField K] (p q : ℕ) : Type (u + 1) :=
  (Fin p → (NormedSpaceCat K)ᵒᵖ) × (Fin q → NormedSpaceCat K)

/-- The hom spaces of `C^ε` in operator coordinates, with the maximum norm. -/
abbrev HomCoords {K : Type u} [NontriviallyNormedField K] {p q : ℕ} (X Y : VarCat K p q) :
    Type u :=
  (∀ a, (Y.1 a).unop →L[K] (X.1 a).unop) × (∀ b, X.2 b →L[K] Y.2 b)

/-- The arrow of `C^ε` with given operator coordinates. -/
def homOfCoords {K : Type u} [NontriviallyNormedField K] {p q : ℕ} {X Y : VarCat K p q}
    (f : HomCoords X Y) : X ⟶ Y :=
  (fun a ↦ Quiver.Hom.op (show (Y.1 a).unop ⟶ (X.1 a).unop from f.1 a),
    fun b ↦ (show X.2 b ⟶ Y.2 b from f.2 b))

/-- `F` is `Cⁿ` on hom spaces. -/
def ContDiffOnHoms {K : Type u} [NontriviallyNormedField K] (n : ℕ∞ω) {p q : ℕ}
    (F : VarCat K p q ⥤ NormedSpaceCat K) : Prop :=
  ∀ X Y : VarCat K p q,
    ContDiff K n (fun f : HomCoords X Y ↦ (F.map (homOfCoords f) : F.obj X →L[K] F.obj Y))

/-- `F` preserves `Cⁿ` families parametrized by open subsets of `P`. -/
def PreservesFamilies {K : Type u} [NontriviallyNormedField K] (n : ℕ∞ω) (P : Type*)
    [NormedAddCommGroup P] [NormedSpace K P] {p q : ℕ}
    (F : VarCat K p q ⥤ NormedSpaceCat K) : Prop :=
  ∀ (X Y : VarCat K p q) (U : Set P), IsOpen U → ∀ γ : P → HomCoords X Y,
    ContDiffOn K n γ U →
      ContDiffOn K n (fun t ↦ (F.map (homOfCoords (γ t)) : F.obj X →L[K] F.obj Y)) U

variable {K : Type u} [NontriviallyNormedField K] {p q : ℕ}

/-- Regularity on whole hom spaces implies preservation of families on open subsets of `P`. -/
theorem preservesFamilies_of_contDiffOnHoms {n : ℕ∞ω} (P : Type*) [NormedAddCommGroup P]
    [NormedSpace K P] {F : VarCat K p q ⥤ NormedSpaceCat K} (hF : ContDiffOnHoms n F) :
    PreservesFamilies n P F :=
  fun X Y _ _ _ hγ ↦ (hF X Y).comp_contDiffOn hγ

/-- Composition in `C^ε` in operator coordinates: reversed in the contravariant variables. -/
theorem homOfCoords_comp {X Y Z : VarCat K p q} (f : HomCoords X Y) (g : HomCoords Y Z) :
    homOfCoords f ≫ homOfCoords g =
      homOfCoords (X := X) (Y := Z) (fun a ↦ (f.1 a).comp (g.1 a), fun b ↦ (g.2 b).comp (f.2 b)) :=
  rfl

/-- The identity of `C^ε` in operator coordinates. -/
theorem homOfCoords_id (X : VarCat K p q) :
    homOfCoords (X := X) (Y := X)
      (fun a ↦ ContinuousLinearMap.id K (X.1 a).unop, fun b ↦ ContinuousLinearMap.id K (X.2 b)) =
      𝟙 X :=
  rfl

end Functors

section Bundles

variable {K : Type u} [NontriviallyNormedField K] {P : Type*} [NormedAddCommGroup P]
  [NormedSpace K P] {M : Type*} [TopologicalSpace M] [ChartedSpace P M] {n : ℕ∞ω} {p q : ℕ}
  (A : Fin p → Type u) [∀ a, NormedAddCommGroup (A a)] [∀ a, NormedSpace K (A a)]
  (EA : Fin p → M → Type u) [∀ a x, TopologicalSpace (EA a x)]
  [∀ a, TopologicalSpace (TotalSpace (A a) (EA a))] [∀ a, FiberBundle (A a) (EA a)]
  (B : Fin q → Type u) [∀ b, NormedAddCommGroup (B b)] [∀ b, NormedSpace K (B b)]
  (EB : Fin q → M → Type u) [∀ b x, TopologicalSpace (EB b x)]
  [∀ b, TopologicalSpace (TotalSpace (B b) (EB b))] [∀ b, FiberBundle (B b) (EB b)]

/-- The model fibers, as an object of `C^ε`. -/
abbrev modelObj : VarCat K p q :=
  (fun a ↦ op (NormedSpaceCat.of K (A a)), fun b ↦ NormedSpaceCat.of K (B b))

/-- The common trivializing cover, indexed by the points of the base. -/
def commonBaseSet (z : M) : Set M :=
  (⋂ a, (trivializationAt (A a) (EA a) z).baseSet) ∩
    ⋂ b, (trivializationAt (B b) (EB b) z).baseSet

variable {A EA B EB} in
/-- The sets of the common cover are open. -/
theorem isOpen_commonBaseSet (z : M) : IsOpen (commonBaseSet A EA B EB z) :=
  (isOpen_iInter_of_finite fun a ↦ (trivializationAt (A a) (EA a) z).open_baseSet).inter
    (isOpen_iInter_of_finite fun b ↦ (trivializationAt (B b) (EB b) z).open_baseSet)

variable {A EA B EB} in
/-- The set of the common cover indexed by `z` contains `z`. -/
theorem mem_commonBaseSet_self (z : M) : z ∈ commonBaseSet A EA B EB z :=
  ⟨mem_iInter.2 fun a ↦ mem_baseSet_trivializationAt (A a) (EA a) z,
    mem_iInter.2 fun b ↦ mem_baseSet_trivializationAt (B b) (EB b) z⟩

variable {A EA B EB} in
/-- The common cover refines the cover of each contravariant bundle. -/
theorem mem_baseSet_left {z x : M} (hx : x ∈ commonBaseSet A EA B EB z) (a : Fin p) :
    x ∈ (trivializationAt (A a) (EA a) z).baseSet :=
  mem_iInter.1 hx.1 a

variable {A EA B EB} in
/-- The common cover refines the cover of each covariant bundle. -/
theorem mem_baseSet_right {z x : M} (hx : x ∈ commonBaseSet A EA B EB z) (b : Fin q) :
    x ∈ (trivializationAt (B b) (EB b) z).baseSet :=
  mem_iInter.1 hx.2 b

variable [∀ a x, AddCommGroup (EA a x)] [∀ a x, Module K (EA a x)]
  [∀ a, VectorBundle K (A a) (EA a)]
  [∀ b x, AddCommGroup (EB b x)] [∀ b x, Module K (EB b x)] [∀ b, VectorBundle K (B b) (EB b)]

/-- The input transitions from the chart at `z` to the chart at `w`, at `x`; reversed in the
contravariant variables. -/
def transition (z w x : M) : HomCoords (modelObj (K := K) A B) (modelObj A B) :=
  (fun a ↦ ((trivializationAt (A a) (EA a) w).coordChangeL K
      (trivializationAt (A a) (EA a) z) x : A a →L[K] A a),
    fun b ↦ ((trivializationAt (B b) (EB b) z).coordChangeL K
      (trivializationAt (B b) (EB b) w) x : B b →L[K] B b))

section Trivializations

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace K F] {E : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module K (E x)] [TopologicalSpace (TotalSpace F E)]

/-- A trivialization change from a chart to itself is the identity on the base set. -/
theorem coordChangeL_self_apply (e : Trivialization F (π F E)) [e.IsLinear K] {x : M}
    (hx : x ∈ e.baseSet) (v : F) : e.coordChangeL K e x v = v :=
  (e.coordChangeL_apply (R := K) e ⟨hx, hx⟩ v).trans (congrArg Prod.snd (e.apply_mk_symm hx v))

/-- The cocycle identity for trivialization changes. -/
theorem coordChangeL_comp_apply (e₁ e₂ e₃ : Trivialization F (π F E)) [e₁.IsLinear K]
    [e₂.IsLinear K] [e₃.IsLinear K] {x : M} (h₁ : x ∈ e₁.baseSet) (h₂ : x ∈ e₂.baseSet)
    (h₃ : x ∈ e₃.baseSet) (v : F) :
    e₂.coordChangeL K e₃ x (e₁.coordChangeL K e₂ x v) = e₁.coordChangeL K e₃ x v := by
  rw [Trivialization.coordChangeL_apply (R := K) _ _ ⟨h₁, h₂⟩,
    Trivialization.coordChangeL_apply (R := K) _ _ ⟨h₂, h₃⟩,
    Trivialization.coordChangeL_apply (R := K) _ _ ⟨h₁, h₃⟩,
    Trivialization.symm_apply_apply_mk _ h₂]

end Trivializations

variable {A EA B EB}

/-- The input transitions from a chart to itself are the identity. -/
theorem homOfCoords_transition_self {z x : M} (hx : x ∈ commonBaseSet A EA B EB z) :
    homOfCoords (transition (K := K) A EA B EB z z x) = 𝟙 (modelObj A B) := by
  refine Prod.ext (funext fun a ↦ Quiver.Hom.unop_inj ?_) (funext fun b ↦ ?_)
  · exact ContinuousLinearMap.ext fun v ↦ coordChangeL_self_apply _ (mem_baseSet_left hx a) v
  · exact ContinuousLinearMap.ext fun v ↦ coordChangeL_self_apply _ (mem_baseSet_right hx b) v

/-- The input transitions satisfy the cocycle identity in `C^ε`. -/
theorem homOfCoords_transition_comp {z w y x : M}
    (hx : x ∈ commonBaseSet A EA B EB z ∩ commonBaseSet A EA B EB w ∩
      commonBaseSet A EA B EB y) :
    homOfCoords (transition (K := K) A EA B EB z w x) ≫
        homOfCoords (transition A EA B EB w y x) =
      homOfCoords (transition A EA B EB z y x) := by
  refine Prod.ext (funext fun a ↦ Quiver.Hom.unop_inj ?_) (funext fun b ↦ ?_)
  · exact ContinuousLinearMap.ext fun v ↦ coordChangeL_comp_apply _ _ _
      (mem_baseSet_left hx.2 a) (mem_baseSet_left hx.1.2 a) (mem_baseSet_left hx.1.1 a) v
  · exact ContinuousLinearMap.ext fun v ↦ coordChangeL_comp_apply _ _ _
      (mem_baseSet_right hx.1.1 b) (mem_baseSet_right hx.1.2 b) (mem_baseSet_right hx.2 b) v

variable (A EA B EB)

/-- The transition functions of `F_M(V)`: `F` applied to the input transitions. -/
def liftCoordChange (F : VarCat K p q ⥤ NormedSpaceCat K) (z w x : M) :
    F.obj (modelObj A B) →L[K] F.obj (modelObj A B) :=
  F.map (homOfCoords (transition A EA B EB z w x))

/-- Continuity of the lifted transition functions on the common overlaps. -/
abbrev LiftContinuous (F : VarCat K p q ⥤ NormedSpaceCat K) : Prop :=
  ∀ z w : M, ContinuousOn (liftCoordChange A EA B EB F z w)
    (commonBaseSet A EA B EB z ∩ commonBaseSet A EA B EB w)

/-- The bundle `F_M(V)`, glued from the transition functions `F(g_zw)` on the common cover.
Continuity of the transition functions is an argument. -/
def liftCore (F : VarCat K p q ⥤ NormedSpaceCat K) (hV : LiftContinuous A EA B EB F) :
    VectorBundleCore K M (F.obj (modelObj A B)) M where
  baseSet := commonBaseSet A EA B EB
  isOpen_baseSet := isOpen_commonBaseSet
  indexAt := id
  mem_baseSet_at := mem_commonBaseSet_self
  coordChange := liftCoordChange A EA B EB F
  coordChange_self z x hx v := by
    change F.map (homOfCoords (transition A EA B EB z z x)) v = v
    rw [homOfCoords_transition_self hx, F.map_id]
    rfl
  continuousOn_coordChange := hV
  coordChange_comp z w y x hx v := by
    change F.map (homOfCoords (transition A EA B EB w y x))
        (F.map (homOfCoords (transition A EA B EB z w x)) v) =
      F.map (homOfCoords (transition A EA B EB z y x)) v
    rw [← homOfCoords_transition_comp hx, F.map_comp]
    rfl

variable {A EA B EB}

/-- The base sets of `F_M(V)` are the common cover. -/
@[simp]
theorem liftCore_baseSet (F : VarCat K p q ⥤ NormedSpaceCat K)
    (hV : LiftContinuous A EA B EB F) :
    (liftCore A EA B EB F hV).baseSet = commonBaseSet A EA B EB := rfl

/-- The chart of `F_M(V)` at a point is indexed by that point. -/
@[simp]
theorem liftCore_indexAt (F : VarCat K p q ⥤ NormedSpaceCat K)
    (hV : LiftContinuous A EA B EB F) :
    (liftCore A EA B EB F hV).indexAt = id := rfl

/-- The transition functions of `F_M(V)` are `F` applied to the input transitions. -/
@[simp]
theorem liftCore_coordChange (F : VarCat K p q ⥤ NormedSpaceCat K)
    (hV : LiftContinuous A EA B EB F) :
    (liftCore A EA B EB F hV).coordChange = liftCoordChange A EA B EB F := rfl

variable [∀ a, ContMDiffVectorBundle (𝕜 := K) n (A a) (EA a) 𝓘(K, P)]
  [∀ b, ContMDiffVectorBundle (𝕜 := K) n (B b) (EB b) 𝓘(K, P)]

/-- The input transitions are `Cⁿ` on the common overlaps. -/
theorem contMDiffOn_transition (z w : M) :
    ContMDiffOn 𝓘(K, P) 𝓘(K, HomCoords (modelObj (K := K) A B) (modelObj A B)) n
      (transition (K := K) A EA B EB z w)
      (commonBaseSet A EA B EB z ∩ commonBaseSet A EA B EB w) := by
  refine ContMDiffOn.prodMk_space (contMDiffOn_pi_space.2 fun a ↦ ?_)
    (contMDiffOn_pi_space.2 fun b ↦ ?_)
  · exact (contMDiffOn_coordChangeL (trivializationAt (A a) (EA a) w)
      (trivializationAt (A a) (EA a) z)).mono fun x hx ↦
        ⟨mem_baseSet_left hx.2 a, mem_baseSet_left hx.1 a⟩
  · exact (contMDiffOn_coordChangeL (trivializationAt (B b) (EB b) z)
      (trivializationAt (B b) (EB b) w)).mono fun x hx ↦
        ⟨mem_baseSet_right hx.1 b, mem_baseSet_right hx.2 b⟩

/-- Under family preservation the lifted transition functions are `Cⁿ`. -/
theorem contMDiffOn_liftCoordChange [IsManifold 𝓘(K, P) n M]
    {F : VarCat K p q ⥤ NormedSpaceCat K} (hF : PreservesFamilies n P F) (z w : M) :
    ContMDiffOn 𝓘(K, P) 𝓘(K, F.obj (modelObj (K := K) A B) →L[K] F.obj (modelObj A B)) n
      (liftCoordChange A EA B EB F z w)
      (commonBaseSet A EA B EB z ∩ commonBaseSet A EA B EB w) :=
  contMDiffOn_comp_of_preservesFamilies
    (Φ := fun f ↦ (F.map (homOfCoords f) : F.obj (modelObj A B) →L[K] F.obj (modelObj A B)))
    (hF (modelObj A B) (modelObj A B))
    ((isOpen_commonBaseSet z).inter (isOpen_commonBaseSet w)) (contMDiffOn_transition z w)

/-- Under family preservation the lifted transition functions are continuous. -/
theorem continuousOn_liftCoordChange [IsManifold 𝓘(K, P) n M]
    {F : VarCat K p q ⥤ NormedSpaceCat K} (hF : PreservesFamilies n P F) (z w : M) :
    ContinuousOn (liftCoordChange A EA B EB F z w)
      (commonBaseSet A EA B EB z ∩ commonBaseSet A EA B EB w) :=
  (contMDiffOn_liftCoordChange hF z w).continuousOn

/-- Under family preservation the glued bundle `F_M(V)` has `Cⁿ` transition functions. -/
theorem liftCore_isContMDiff [IsManifold 𝓘(K, P) n M]
    {F : VarCat K p q ⥤ NormedSpaceCat K} (hF : PreservesFamilies n P F)
    (hV : LiftContinuous A EA B EB F) :
    (liftCore A EA B EB F hV).IsContMDiff 𝓘(K, P) n :=
  ⟨fun z w ↦ contMDiffOn_liftCoordChange hF z w⟩

end Bundles

end AlternatingAnalytic.FunctorLifting
