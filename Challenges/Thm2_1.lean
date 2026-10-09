import AlternatingAnalytic.Analysis.AnalyticFamilies
import AlternatingAnalytic.Category.NormedSpace
import AlternatingAnalytic.Geometry.ContMDiffBundleHom
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Topology.VectorBundle.ContinuousAlternatingMap
import Mathlib.CategoryTheory.Pi.Basic

/-!
# Theorem 2.1 (lifting linear constructions to bundles), pp. 4–5

Setting (Section 2.1). `K` is a nontrivially normed field, `Vec_K` the category of normed
`K`-spaces and bounded linear maps, and `n ∈ ℕ ∪ {∞, ω}`. `VBⁿ_K(M)` is the category of `Cⁿ`
normed vector bundles over a `Cⁿ` manifold `M` modelled on `P`, with morphisms over `id_M` whose
local operator-valued expressions are `Cⁿ`. `C^ε` is a product of copies of `Vec_K` and
`Vec_K^op`; a functor `C^ε → Vec_K` is `Cⁿ` if its maps on products of hom spaces (maximum norm)
are jointly `Cⁿ`; `B^ε_M` is the corresponding product of bundle categories.

Paper statement: "For a fixed `Cⁿ` manifold `M`, fiberwise application defines, up to canonical
natural isomorphism, a functor `Bⁿ_M : Fun^{Cⁿ}(C^ε, Vec_K) → Fun(B^ε_M, VBⁿ_K(M))`,
`F ↦ F_M`, `η ↦ η_M`. Here the category on the left is the full subcategory of the ordinary
functor category on the functors regular on hom spaces. The resulting bundles, bundle
morphisms, and natural transformations are given fiberwise by `F`, its action on maps, and the
components of `η`, respectively. The same conclusion holds if regularity on whole hom spaces is
replaced by preservation of `Cⁿ` families parametrized by open subsets of the model space `P`."

## Formalization notes
* `bundleLifting` (regularity on hom spaces) and `bundleLifting_familywise` (preservation of
  families) are the two forms of the theorem.
* The variables are grouped by variance: `C^ε = (Vec_Kᵒᵖ)^p × Vec_K^q` (`VarCat K p q`). The
  paper allows any order; reordering the factors is an isomorphism of categories.
* `Vec_K` is `NormedSpaceCat K`, the normed spaces in the universe of `K`. The model fibers of the
  bundles lie in that universe.
* `ContDiffOnHoms n F`: each map `Hom(X, Y) → L(F X, F Y)` is `ContDiff` in operator coordinates
  `HomCoords X Y` (maximum norm). `PreservesFamilies n P F` asks this only along families that
  are `ContDiffOn` an open `U ⊆ P`.
* `M` is modelled on `P` without boundary. An object of `VBⁿ_K(M)` (`VB K P M n`) is a Mathlib
  `ContMDiffVectorBundle` with a normed model fiber; the fibers carry no chosen norm. Morphisms
  are `Cⁿ` sections of the Hom bundle.
* `F_M(V)` (`liftCore`) is glued on the cover indexed by the points `z ∈ M` (`commonBaseSet`),
  with transition functions `F(g_zw)` (`liftCoordChange`). Continuity of the transitions is a
  field of Mathlib's `VectorBundleCore`, so `liftCore` takes it as an argument `hV`; the main
  theorems assert that `hV` exists.
* The functor is built from the canonical trivializations `trivializationAt`, so it exists on
  the nose. Independence of the trivializing cover is not stated.
* The fibers of `F_M(T)` and `η_M` are stated with `HEq`, because the object equation is
  propositional. `localTuple T x` is the local expression of `T` at `x`.
* `alternating_object_familywise` is an extra special case (the `Alt^k` bifunctor, objects only)
  over a model with corners. Its families are parametrized by open subsets of `M`, and only
  `L(F₁, F₁) × L(F₂, F₂)` is tested. The general theorems do not use it.
* The two instances on `VectorBundleCore.Fiber` (`IsTopologicalAddGroup`, `ContinuousSMul`) are
  missing from Mathlib and carry no data.
-/

open Bundle
open scoped Bundle Manifold ContDiff

namespace AlternatingAnalyticChallenge.Thm2_1

/-- If the joint action on `Alt^k` preserves `Cⁿ` families on open subsets of the base, the
bundle of continuous alternating maps between two `Cⁿ` vector bundles is a `Cⁿ` vector bundle. -/
theorem alternating_object_familywise
    {K M F₁ F₂ : Type*} [NontriviallyNormedField K] [TopologicalSpace M]
    [NormedAddCommGroup F₁] [NormedSpace K F₁]
    [NormedAddCommGroup F₂] [NormedSpace K F₂]
    {E₁ E₂ : M → Type*}
    [∀ x, AddCommGroup (E₁ x)] [∀ x, Module K (E₁ x)]
    [∀ x, AddCommGroup (E₂ x)] [∀ x, Module K (E₂ x)]
    [TopologicalSpace (TotalSpace F₁ E₁)] [TopologicalSpace (TotalSpace F₂ E₂)]
    [∀ x, TopologicalSpace (E₁ x)] [∀ x, TopologicalSpace (E₂ x)]
    [FiberBundle F₁ E₁] [VectorBundle K F₁ E₁]
    [FiberBundle F₂ E₂] [VectorBundle K F₂ E₂]
    [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul K (E₂ x)]
    {P H : Type*} [NormedAddCommGroup P] [NormedSpace K P]
    [TopologicalSpace H] [ChartedSpace H M] {I : ModelWithCorners K P H} {n : ℕ∞ω}
    [ContMDiffVectorBundle n F₁ E₁ I] [ContMDiffVectorBundle n F₂ E₂ I]
    (k : ℕ)
    (hfamily : ∀ {U : Set M}, IsOpen U →
      ∀ {γ : M → (F₁ →L[K] F₁) × (F₂ →L[K] F₂)},
        ContMDiffOn I 𝓘(K, (F₁ →L[K] F₁) × (F₂ →L[K] F₂)) n γ U →
        ContMDiffOn I 𝓘(K, (F₁ [⋀^Fin k]→L[K] F₂) →L[K] (F₁ [⋀^Fin k]→L[K] F₂))
          n (AlternatingAnalytic.alternatingMapAction k ∘ γ) U) :
    ContMDiffVectorBundle n (F₁ [⋀^Fin k]→L[K] F₂)
      (fun x ↦ E₁ x [⋀^Fin k]→L[K] E₂ x) I := by
  sorry

/-! ### The general theorem -/

open CategoryTheory Opposite AlternatingAnalytic

universe u

section Functors

/-- `C^ε` for `p` contravariant and `q` covariant variables: `(Vec_Kᵒᵖ)^p × Vec_K^q`. -/
abbrev VarCat (K : Type u) [NontriviallyNormedField K] (p q : ℕ) : Type (u + 1) :=
  (Fin p → (NormedSpaceCat K)ᵒᵖ) × (Fin q → NormedSpaceCat K)

/-- The hom space `Hom(X, Y)` of `C^ε` in operator coordinates: the product of the operator
spaces (reversed in the contravariant variables), with the maximum norm. -/
abbrev HomCoords {K : Type u} [NontriviallyNormedField K] {p q : ℕ} (X Y : VarCat K p q) :
    Type u :=
  (∀ a, (Y.1 a).unop →L[K] (X.1 a).unop) × (∀ b, X.2 b →L[K] Y.2 b)

/-- The arrow of `C^ε` with the given operator coordinates. -/
def homOfCoords {K : Type u} [NontriviallyNormedField K] {p q : ℕ} {X Y : VarCat K p q}
    (f : HomCoords X Y) : X ⟶ Y :=
  (fun a ↦ Quiver.Hom.op (show (Y.1 a).unop ⟶ (X.1 a).unop from f.1 a),
    fun b ↦ (show X.2 b ⟶ Y.2 b from f.2 b))

/-- `F : C^ε ⥤ Vec_K` is `Cⁿ` on hom spaces: every map `Hom(X, Y) → L(F X, F Y)` is jointly
`Cⁿ`. -/
def ContDiffOnHoms {K : Type u} [NontriviallyNormedField K] (n : ℕ∞ω) {p q : ℕ}
    (F : VarCat K p q ⥤ NormedSpaceCat K) : Prop :=
  ∀ X Y : VarCat K p q,
    ContDiff K n (fun f : HomCoords X Y ↦ (F.map (homOfCoords f) : F.obj X →L[K] F.obj Y))

/-- `F : C^ε ⥤ Vec_K` preserves `Cⁿ` families parametrized by open subsets of `P`. -/
def PreservesFamilies {K : Type u} [NontriviallyNormedField K] (n : ℕ∞ω) (P : Type*)
    [NormedAddCommGroup P] [NormedSpace K P] {p q : ℕ}
    (F : VarCat K p q ⥤ NormedSpaceCat K) : Prop :=
  ∀ (X Y : VarCat K p q) (U : Set P), IsOpen U → ∀ γ : P → HomCoords X Y,
    ContDiffOn K n γ U →
      ContDiffOn K n (fun t ↦ (F.map (homOfCoords (γ t)) : F.obj X →L[K] F.obj Y)) U

/-- `Fun^{Cⁿ}(C^ε, Vec_K)`: the full subcategory of functors that are `Cⁿ` on hom spaces. -/
abbrev CnFunctorCat (K : Type u) [NontriviallyNormedField K] (n : ℕ∞ω) (p q : ℕ) :
    Type (u + 1) :=
  ObjectProperty.FullSubcategory (ContDiffOnHoms (K := K) (p := p) (q := q) n)

/-- The full subcategory of functors preserving `Cⁿ` families on open subsets of `P`. -/
abbrev FamilyFunctorCat (K : Type u) [NontriviallyNormedField K] (n : ℕ∞ω) (P : Type*)
    [NormedAddCommGroup P] [NormedSpace K P] (p q : ℕ) : Type (u + 1) :=
  ObjectProperty.FullSubcategory (PreservesFamilies (K := K) (p := p) (q := q) n P)

end Functors

noncomputable section Bundles

/-- An object of `VBⁿ_K(M)`: a `Cⁿ` vector bundle over `M` with a normed model fiber. -/
structure VB (K : Type u) [NontriviallyNormedField K] (P : Type*) [NormedAddCommGroup P]
    [NormedSpace K P] (M : Type*) [TopologicalSpace M] [ChartedSpace P M] (n : ℕ∞ω) where
  /-- The normed model fiber. -/
  Model : Type u
  [normedAddCommGroup : NormedAddCommGroup Model]
  [normedSpace : NormedSpace K Model]
  /-- The fibers. -/
  Fiber : M → Type u
  [addCommGroup : ∀ x, AddCommGroup (Fiber x)]
  [module : ∀ x, Module K (Fiber x)]
  [topologicalSpace : ∀ x, TopologicalSpace (Fiber x)]
  [isTopologicalAddGroup : ∀ x, IsTopologicalAddGroup (Fiber x)]
  [continuousSMul : ∀ x, ContinuousSMul K (Fiber x)]
  [totalSpaceTopology : TopologicalSpace (TotalSpace Model Fiber)]
  [fiberBundle : FiberBundle Model Fiber]
  [vectorBundle : VectorBundle K Model Fiber]
  [contMDiffVectorBundle : ContMDiffVectorBundle n Model Fiber 𝓘(K, P)]

attribute [instance] VB.normedAddCommGroup VB.normedSpace VB.addCommGroup VB.module
  VB.topologicalSpace VB.isTopologicalAddGroup VB.continuousSMul VB.totalSpaceTopology
  VB.fiberBundle VB.vectorBundle VB.contMDiffVectorBundle

variable {K : Type u} [NontriviallyNormedField K] {P : Type*} [NormedAddCommGroup P]
  [NormedSpace K P] {M : Type*} [TopologicalSpace M] [ChartedSpace P M] {n : ℕ∞ω}

/-- `VBⁿ_K(M)`: morphisms are `Cⁿ` sections of the Hom bundle. -/
instance : Category (VB K P M n) where
  Hom X Y :=
    ContMDiffSection 𝓘(K, P) (X.Model →L[K] Y.Model) n (fun x ↦ X.Fiber x →L[K] Y.Fiber x)
  id X := contMDiffHomId X.Model X.Fiber
  comp f g := contMDiffHomComp f g
  id_comp f := ContMDiffSection.ext fun x ↦ ContinuousLinearMap.comp_id (f x)
  comp_id f := ContMDiffSection.ext fun x ↦ ContinuousLinearMap.id_comp (f x)
  assoc f g h := ContMDiffSection.ext fun x ↦
    (ContinuousLinearMap.comp_assoc (h x) (g x) (f x)).symm

instance (X Y : VB K P M n) : DFunLike (X ⟶ Y) M (fun x ↦ X.Fiber x →L[K] Y.Fiber x) :=
  inferInstanceAs (DFunLike (ContMDiffSection 𝓘(K, P) (X.Model →L[K] Y.Model) n
    (fun x ↦ X.Fiber x →L[K] Y.Fiber x)) M _)

instance {ι F : Type*} [NormedAddCommGroup F] [NormedSpace K F]
    (Z : VectorBundleCore K M F ι) (x : M) : IsTopologicalAddGroup (Z.Fiber x) :=
  inferInstanceAs (IsTopologicalAddGroup F)

instance {ι F : Type*} [NormedAddCommGroup F] [NormedSpace K F]
    (Z : VectorBundleCore K M F ι) (x : M) : ContinuousSMul K (Z.Fiber x) :=
  inferInstanceAs (ContinuousSMul K F)

variable (K P M n) in
/-- `B^ε_M`: `p` contravariant and `q` covariant bundle variables, `(VBᵒᵖ)^p × VB^q`. -/
abbrev BundleVarCat (p q : ℕ) : Type _ :=
  (Fin p → (VB K P M n)ᵒᵖ) × (Fin q → VB K P M n)

variable {p q : ℕ}

/-- The model fibers of a tuple of bundles, as an object of `C^ε`. -/
abbrev modelObj (V : BundleVarCat K P M n p q) : VarCat K p q :=
  (fun a ↦ op (NormedSpaceCat.of K (V.1 a).unop.Model),
    fun b ↦ NormedSpaceCat.of K (V.2 b).Model)

/-- The common trivializing cover, indexed by the points `z` of the base: the intersection of
the base sets of the trivializations at `z` of all the bundles. -/
def commonBaseSet (V : BundleVarCat K P M n p q) (z : M) : Set M :=
  (⋂ a, (trivializationAt (V.1 a).unop.Model (V.1 a).unop.Fiber z).baseSet) ∩
    ⋂ b, (trivializationAt (V.2 b).Model (V.2 b).Fiber z).baseSet

/-- The input transitions from the chart at `z` to the chart at `w`, at `x`: from `z` to `w` in
the covariant variables, from `w` to `z` in the contravariant ones. -/
def transition (V : BundleVarCat K P M n p q) (z w x : M) :
    HomCoords (modelObj V) (modelObj V) :=
  (fun a ↦ ((trivializationAt (V.1 a).unop.Model (V.1 a).unop.Fiber w).coordChangeL K
      (trivializationAt (V.1 a).unop.Model (V.1 a).unop.Fiber z) x :
        (V.1 a).unop.Model →L[K] (V.1 a).unop.Model),
    fun b ↦ ((trivializationAt (V.2 b).Model (V.2 b).Fiber z).coordChangeL K
      (trivializationAt (V.2 b).Model (V.2 b).Fiber w) x : (V.2 b).Model →L[K] (V.2 b).Model))

/-- The transition functions of `F_M(V)`: `θ_zw(x) = F(g_zw(x))`. -/
def liftCoordChange (F : VarCat K p q ⥤ NormedSpaceCat K) (V : BundleVarCat K P M n p q)
    (z w x : M) : F.obj (modelObj V) →L[K] F.obj (modelObj V) :=
  F.map (homOfCoords (transition V z w x))

/-- Continuity of the transition functions of `F_M(V)` on the overlaps. -/
abbrev LiftContinuous (F : VarCat K p q ⥤ NormedSpaceCat K) (V : BundleVarCat K P M n p q) :
    Prop :=
  ∀ z w : M, ContinuousOn (liftCoordChange F V z w) (commonBaseSet V z ∩ commonBaseSet V w)

/-- The bundle `F_M(V)`, glued from the transition functions `F(g_zw)` on the common cover. The
cocycle identities follow from functoriality; continuity is the argument `hV`. -/
def liftCore (F : VarCat K p q ⥤ NormedSpaceCat K) (V : BundleVarCat K P M n p q)
    (hV : LiftContinuous F V) : VectorBundleCore K M (F.obj (modelObj V)) M where
  baseSet := commonBaseSet V
  isOpen_baseSet z :=
    (isOpen_iInter_of_finite fun a ↦
      (trivializationAt (V.1 a).unop.Model (V.1 a).unop.Fiber z).open_baseSet).inter
    (isOpen_iInter_of_finite fun b ↦
      (trivializationAt (V.2 b).Model (V.2 b).Fiber z).open_baseSet)
  indexAt := id
  mem_baseSet_at z :=
    ⟨Set.mem_iInter.2 fun a ↦ mem_baseSet_trivializationAt (V.1 a).unop.Model _ z,
      Set.mem_iInter.2 fun b ↦ mem_baseSet_trivializationAt (V.2 b).Model _ z⟩
  coordChange := liftCoordChange F V
  coordChange_self z x hx v := by
    have h : homOfCoords (transition V z z x) = 𝟙 (modelObj V) := by
      refine Prod.ext (funext fun a ↦ Quiver.Hom.unop_inj ?_) (funext fun b ↦ ?_)
      · have hxa := Set.mem_iInter.1 hx.1 a
        exact ContinuousLinearMap.ext fun v ↦
          ((trivializationAt _ _ z).coordChangeL_apply (R := K) _ ⟨hxa, hxa⟩ v).trans
            (congrArg Prod.snd ((trivializationAt _ _ z).apply_mk_symm hxa v))
      · have hxb := Set.mem_iInter.1 hx.2 b
        exact ContinuousLinearMap.ext fun v ↦
          ((trivializationAt _ _ z).coordChangeL_apply (R := K) _ ⟨hxb, hxb⟩ v).trans
            (congrArg Prod.snd ((trivializationAt _ _ z).apply_mk_symm hxb v))
    change F.map (homOfCoords (transition V z z x)) v = v
    rw [h, F.map_id]
    rfl
  continuousOn_coordChange := hV
  coordChange_comp z w y x hx v := by
    have h : homOfCoords (transition V z w x) ≫ homOfCoords (transition V w y x) =
        homOfCoords (transition V z y x) := by
      refine Prod.ext (funext fun a ↦ Quiver.Hom.unop_inj ?_) (funext fun b ↦ ?_)
      · have hz := Set.mem_iInter.1 hx.1.1.1 a
        have hw := Set.mem_iInter.1 hx.1.2.1 a
        have hy := Set.mem_iInter.1 hx.2.1 a
        refine ContinuousLinearMap.ext fun (v : (V.1 a).unop.Model) ↦ ?_
        change (trivializationAt (V.1 a).unop.Model (V.1 a).unop.Fiber w).coordChangeL K
            (trivializationAt (V.1 a).unop.Model (V.1 a).unop.Fiber z) x
            ((trivializationAt (V.1 a).unop.Model (V.1 a).unop.Fiber y).coordChangeL K
              (trivializationAt (V.1 a).unop.Model (V.1 a).unop.Fiber w) x v) =
          (trivializationAt (V.1 a).unop.Model (V.1 a).unop.Fiber y).coordChangeL K
            (trivializationAt (V.1 a).unop.Model (V.1 a).unop.Fiber z) x v
        rw [Trivialization.coordChangeL_apply (R := K) _ _ ⟨hy, hw⟩,
          Trivialization.coordChangeL_apply (R := K) _ _ ⟨hw, hz⟩,
          Trivialization.coordChangeL_apply (R := K) _ _ ⟨hy, hz⟩,
          Trivialization.symm_apply_apply_mk _ hw]
      · have hz := Set.mem_iInter.1 hx.1.1.2 b
        have hw := Set.mem_iInter.1 hx.1.2.2 b
        have hy := Set.mem_iInter.1 hx.2.2 b
        refine ContinuousLinearMap.ext fun (v : (V.2 b).Model) ↦ ?_
        change (trivializationAt (V.2 b).Model (V.2 b).Fiber w).coordChangeL K
            (trivializationAt (V.2 b).Model (V.2 b).Fiber y) x
            ((trivializationAt (V.2 b).Model (V.2 b).Fiber z).coordChangeL K
              (trivializationAt (V.2 b).Model (V.2 b).Fiber w) x v) =
          (trivializationAt (V.2 b).Model (V.2 b).Fiber z).coordChangeL K
            (trivializationAt (V.2 b).Model (V.2 b).Fiber y) x v
        rw [Trivialization.coordChangeL_apply (R := K) _ _ ⟨hz, hw⟩,
          Trivialization.coordChangeL_apply (R := K) _ _ ⟨hw, hy⟩,
          Trivialization.coordChangeL_apply (R := K) _ _ ⟨hz, hy⟩,
          Trivialization.symm_apply_apply_mk _ hw]
    change F.map (homOfCoords (transition V w y x))
        (F.map (homOfCoords (transition V z w x)) v) =
      F.map (homOfCoords (transition V z y x)) v
    rw [← h, F.map_comp]
    rfl

/-- `F_M(V)` as an object of `VBⁿ_K(M)`, given that its transition functions are `Cⁿ`. -/
def liftObj (F : VarCat K p q ⥤ NormedSpaceCat K) (V : BundleVarCat K P M n p q)
    (hV : LiftContinuous F V)
    (h : ContMDiffVectorBundle n (F.obj (modelObj V)) (liftCore F V hV).Fiber 𝓘(K, P)) :
    VB K P M n where
  Model := F.obj (modelObj V)
  Fiber := (liftCore F V hV).Fiber
  contMDiffVectorBundle := h

/-- The local operator expressions at `x` of a tuple of bundle morphisms, in the trivializations
at `x` (the morphisms go backwards in the contravariant variables). -/
def localTuple {V V' : BundleVarCat K P M n p q} (T : V ⟶ V') (x : M) :
    HomCoords (modelObj V) (modelObj V') :=
  (fun a ↦ ContinuousLinearMap.inCoordinates (V'.1 a).unop.Model (V'.1 a).unop.Fiber
      (V.1 a).unop.Model (V.1 a).unop.Fiber x x x x ((T.1 a).unop x),
    fun b ↦ ContinuousLinearMap.inCoordinates (V.2 b).Model (V.2 b).Fiber
      (V'.2 b).Model (V'.2 b).Fiber x x x x ((T.2 b) x))

/-- Regularity on whole hom spaces implies preservation of `Cⁿ` families on open subsets of
`P`. -/
theorem preservesFamilies_of_contDiffOnHoms {F : VarCat K p q ⥤ NormedSpaceCat K}
    (hF : ContDiffOnHoms n F) : PreservesFamilies n P F := by
  sorry

/-- For a functor preserving `Cⁿ` families, the transition functions `F(g_zw)` of `F_M(V)` are
continuous. -/
theorem liftContinuous [IsManifold 𝓘(K, P) n M] {F : VarCat K p q ⥤ NormedSpaceCat K}
    (hF : PreservesFamilies n P F) (V : BundleVarCat K P M n p q) : LiftContinuous F V := by
  sorry

/-- For a functor preserving `Cⁿ` families, the glued bundle `F_M(V)` has `Cⁿ` transition
functions, so it is a `Cⁿ` vector bundle. -/
theorem liftCore_isContMDiff [IsManifold 𝓘(K, P) n M] {F : VarCat K p q ⥤ NormedSpaceCat K}
    (hF : PreservesFamilies n P F) (V : BundleVarCat K P M n p q) (hV : LiftContinuous F V) :
    (liftCore F V hV).IsContMDiff 𝓘(K, P) n ∧
      ContMDiffVectorBundle n (F.obj (modelObj V)) (liftCore F V hV).Fiber 𝓘(K, P) := by
  sorry

/-- Fiberwise application defines a functor `Bⁿ_M : Fun^{Cⁿ}(C^ε, Vec_K) ⥤ Fun(B^ε_M, VBⁿ_K(M))`.
Its object at `(F, V)` is the bundle glued from `F(g_zw)`, and the fibers of `F_M(T)` and `η_M`
at `x` are `F(T(x))` and `η_{(E₁, …, E_r)}`. -/
theorem bundleLifting [IsManifold 𝓘(K, P) n M] :
    ∃ 𝓑 : CnFunctorCat K n p q ⥤ (BundleVarCat K P M n p q ⥤ VB K P M n),
      (∀ (F : CnFunctorCat K n p q) (V : BundleVarCat K P M n p q),
        ∃ (hV : LiftContinuous F.obj V)
          (h : ContMDiffVectorBundle n (F.obj.obj (modelObj V)) (liftCore F.obj V hV).Fiber
            𝓘(K, P)),
          (𝓑.obj F).obj V = liftObj F.obj V hV h) ∧
      (∀ (F : CnFunctorCat K n p q) {V V' : BundleVarCat K P M n p q} (T : V ⟶ V') (x : M),
        HEq ((𝓑.obj F).map T x) (F.obj.map (homOfCoords (localTuple T x)))) ∧
      (∀ {F G : CnFunctorCat K n p q} (η : F ⟶ G) (V : BundleVarCat K P M n p q) (x : M),
        HEq ((𝓑.map η).app V x) (η.hom.app (modelObj V))) := by
  sorry

/-- The same conclusion for functors that preserve `Cⁿ` families parametrized by open subsets of
the model space `P`. -/
theorem bundleLifting_familywise [IsManifold 𝓘(K, P) n M] :
    ∃ 𝓑 : FamilyFunctorCat K n P p q ⥤ (BundleVarCat K P M n p q ⥤ VB K P M n),
      (∀ (F : FamilyFunctorCat K n P p q) (V : BundleVarCat K P M n p q),
        ∃ (hV : LiftContinuous F.obj V)
          (h : ContMDiffVectorBundle n (F.obj.obj (modelObj V)) (liftCore F.obj V hV).Fiber
            𝓘(K, P)),
          (𝓑.obj F).obj V = liftObj F.obj V hV h) ∧
      (∀ (F : FamilyFunctorCat K n P p q) {V V' : BundleVarCat K P M n p q} (T : V ⟶ V')
          (x : M),
        HEq ((𝓑.obj F).map T x) (F.obj.map (homOfCoords (localTuple T x)))) ∧
      (∀ {F G : FamilyFunctorCat K n P p q} (η : F ⟶ G) (V : BundleVarCat K P M n p q) (x : M),
        HEq ((𝓑.map η).app V x) (η.hom.app (modelObj V))) := by
  sorry

end Bundles

end AlternatingAnalyticChallenge.Thm2_1
