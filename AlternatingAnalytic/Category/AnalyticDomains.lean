import AlternatingAnalytic.Category.AlternatingFunctor
import AlternatingAnalytic.Analysis.UniversalAlternatingTargets
import AlternatingAnalytic.Analysis.SplitAlternatingPairs

/-!
# Universal-target core and split-pair analytic domains

All carriers and the field lie in `Type u`. An analytic domain tests every hom
space of the actual full restriction of `alternatingFunctor`, including homs
between distinct objects. The full-subcategory and opposite wrappers retain
the canonical operator norms, with the maximum norm on pairs of operators.

This file proves `dom:core` and `dom:split-incoming` from `paper/charp.tex`.
The product characterization concerns unrestricted first factors only.
-/

noncomputable section

open CategoryTheory Opposite

universe u

namespace AlternatingAnalytic

variable (K : Type u) [NontriviallyNormedField K] (k : ℕ)

namespace NormedSpaceCat

variable {K}

/-- Remove the full-subcategory wrapper, then use the canonical opposite/product
coordinates. The first operator goes from the destination source to the source source. -/
def restrictedPairHomEquiv
    (S : ObjectProperty ((NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K))
    (X Y : S.FullSubcategory) :
    (X ⟶ Y) ≃ (Y.obj.1.unop →L[K] X.obj.1.unop) × (X.obj.2 →L[K] Y.obj.2) :=
  InducedCategory.homEquiv.trans (pairHomCoordinates X.obj Y.obj).toEquiv

instance restrictedPairHomNormedAddCommGroup
    (S : ObjectProperty ((NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K))
    (X Y : S.FullSubcategory) : NormedAddCommGroup (X ⟶ Y) :=
  (restrictedPairHomEquiv S X Y).normedAddCommGroup

instance restrictedPairHomNormedSpace
    (S : ObjectProperty ((NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K))
    (X Y : S.FullSubcategory) : NormedSpace K (X ⟶ Y) where
  __ := (restrictedPairHomEquiv S X Y).addEquiv.module K
  norm_smul_le c f := by
    change ‖c • restrictedPairHomEquiv S X Y f‖ ≤
      ‖c‖ * ‖restrictedPairHomEquiv S X Y f‖
    exact norm_smul_le c (restrictedPairHomEquiv S X Y f)

/-- Isometric operator coordinates for a full subcategory of the product. -/
def restrictedPairHomCoordinates
    (S : ObjectProperty ((NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K))
    (X Y : S.FullSubcategory) :
    (X ⟶ Y) ≃ₗᵢ[K]
      (Y.obj.1.unop →L[K] X.obj.1.unop) × (X.obj.2 →L[K] Y.obj.2) where
  __ := (restrictedPairHomEquiv S X Y).addEquiv.linearEquiv K
  norm_map' _ := rfl

@[simp]
theorem restrictedPairHomCoordinates_apply
    (S : ObjectProperty ((NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K))
    {X Y : S.FullSubcategory} (f : X ⟶ Y) :
    restrictedPairHomCoordinates S X Y f = (f.hom.1.unop, f.hom.2) := rfl

@[simp]
theorem restrictedPairHomCoordinates_symm_apply
    (S : ObjectProperty ((NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K))
    (X Y : S.FullSubcategory)
    (z : (Y.obj.1.unop →L[K] X.obj.1.unop) × (X.obj.2 →L[K] Y.obj.2)) :
    (restrictedPairHomCoordinates S X Y).symm z =
      ObjectProperty.homMk ((pairHomCoordinates X.obj Y.obj).symm z) := rfl

/-- The inclusion changes neither the linear coordinates nor the operator norms. -/
theorem restrictedPairHomCoordinates_inclusion
    (S : ObjectProperty ((NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K))
    {X Y : S.FullSubcategory} (f : X ⟶ Y) :
    pairHomCoordinates X.obj Y.obj (S.ι.map f) =
      restrictedPairHomCoordinates S X Y f := rfl

theorem norm_restrictedPair_hom
    (S : ObjectProperty ((NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K))
    {X Y : S.FullSubcategory} (f : X ⟶ Y) :
    ‖f‖ = max ‖f.hom.1.unop‖ ‖f.hom.2‖ := rfl

end NormedSpaceCat

/-- The actual full restriction, with all cross-object morphisms. -/
abbrev restrictedAlternatingFunctor
    (S : ObjectProperty ((NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K)) :=
  S.ι ⋙ alternatingFunctor K k

/-- The restricted functor's actual hom map in canonical operator coordinates. -/
theorem restrictedAlternatingFunctor_mapInCoordinates
    (S : ObjectProperty ((NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K))
    (X Y : S.FullSubcategory) :
    functorMapInCoordinates (restrictedAlternatingFunctor K k S)
      (NormedSpaceCat.restrictedPairHomCoordinates S X Y)
      (NormedSpaceCat.homCoordinates
        ((restrictedAlternatingFunctor K k S).obj X)
        ((restrictedAlternatingFunctor K k S).obj Y)) =
      alternatingMapAction k := rfl

/-- An analytic domain means joint analyticity on every actual restricted hom space. -/
def IsAlternatingAnalyticDomain
    (S : ObjectProperty ((NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K)) : Prop :=
  FunctorAnalyticOnHoms K (S.ι ⋙ alternatingFunctor K k)

theorem isAlternatingAnalyticDomain_iff_functorAnalyticOnHoms
    (S : ObjectProperty ((NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K)) :
    IsAlternatingAnalyticDomain K k S ↔
      FunctorAnalyticOnHoms K (S.ι ⋙ alternatingFunctor K k) := Iff.rfl

/-- Fullness allows arbitrary pairs of objects satisfying `S`, not just endomorphisms. -/
theorem isAlternatingAnalyticDomain_iff_coordinates
    (S : ObjectProperty ((NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K)) :
    IsAlternatingAnalyticDomain K k S ↔
      ∀ (X Y : (NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K), S X → S Y →
        AnalyticOnNhd K (alternatingMapAction (K := K)
          (E := X.1.unop) (E' := Y.1.unop) (F := X.2) (F' := Y.2) k) Set.univ := by
  unfold IsAlternatingAnalyticDomain
  rw [functorAnalyticOnHoms_iff_mapInCoordinates
    (e := NormedSpaceCat.restrictedPairHomCoordinates S)
    (e' := fun _ _ => NormedSpaceCat.homCoordinates _ _)]
  simp only [restrictedAlternatingFunctor_mapInCoordinates]
  constructor
  · intro h X Y hX hY
    exact h ⟨X, hX⟩ ⟨Y, hY⟩
  · intro h X Y
    exact h X.obj Y.obj X.property Y.property

/-- The target property defining the full category `T_k(K)`. -/
def isUniversalAlternatingTarget : ObjectProperty (NormedSpaceCat K) :=
  fun F => UniversalAlternatingTarget K k F

/-- The actual full category of universal alternating targets. -/
abbrev UniversalAlternatingTargetCat := (isUniversalAlternatingTarget K k).FullSubcategory

/-- The fully faithful inclusion of universal targets into normed spaces. -/
abbrev UniversalAlternatingTargetCat.inclusion :
    UniversalAlternatingTargetCat K k ⥤ NormedSpaceCat K :=
  (isUniversalAlternatingTarget K k).ι

/-- The universal-target core has an unrestricted contravariant first factor. -/
def universalTargetCore : ObjectProperty ((NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K) :=
  fun X => UniversalAlternatingTarget K k X.2

abbrev UniversalTargetCoreCat := (universalTargetCore K k).FullSubcategory

/-- The actual full category of pairs whose alternating inclusion has a bounded retraction. -/
def splitPairs : ObjectProperty ((NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K) :=
  fun X => IsSplitAlternatingPair K k X.1.unop X.2

abbrev SplitAlternatingPairCat := (splitPairs K k).FullSubcategory

/-- A universal target at either endpoint makes the actual hom action analytic. -/
theorem alternatingFunctor_analyticOnNhd_hom_of_universal_target
    (X Y : (NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K)
    (h : universalTargetCore K k X ∨ universalTargetCore K k Y) :
    AnalyticOnNhd K (fun f : X ⟶ Y => (alternatingFunctor K k).map f) Set.univ := by
  apply (analyticOnNhd_functorMapInCoordinates_iff (alternatingFunctor K k)
    (NormedSpaceCat.pairHomCoordinates X Y)
    (NormedSpaceCat.homCoordinates _ _)).1
  rw [alternatingFunctor_mapInCoordinates]
  exact analyticOnNhd_alternatingMapAction_of_universal_target k h

theorem universalTargetCore_isAnalyticDomain :
    IsAlternatingAnalyticDomain K k (universalTargetCore K k) := by
  apply (isAlternatingAnalyticDomain_iff_coordinates K k _).2
  intro X Y hX _
  exact analyticOnNhd_alternatingMapAction_of_universal_target k (Or.inl hX)

/-- Largest among analytic domains with unrestricted first factor.
The converse uses the affine slice `u ↦ (u, id_F)` between `(op D,F)` and
`(op E,F)` for arbitrary, independently chosen normed spaces `E` and `D`. -/
theorem product_isAnalyticDomain_iff (T : ObjectProperty (NormedSpaceCat K)) :
    IsAlternatingAnalyticDomain K k (fun X => T X.2) ↔
      ∀ F, T F → UniversalAlternatingTarget K k F := by
  rw [isAlternatingAnalyticDomain_iff_coordinates]
  constructor
  · intro h F hF E D _ _ _ _ u _
    apply analyticAt_precomposition_of_analyticAt_alternatingMapAction k u
    exact h (op (NormedSpaceCat.of K D), F) (op (NormedSpaceCat.of K E), F)
      hF hF (u, ContinuousLinearMap.id K F) (Set.mem_univ _)
  · intro h X Y hX _
    exact analyticOnNhd_alternatingMapAction_of_universal_target k (Or.inl (h X.2 hX))

/-- Adjoining the core preserves all cross-object hom actions. -/
theorem IsAlternatingAnalyticDomain.union_core
    {S : ObjectProperty ((NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K)}
    (hS : IsAlternatingAnalyticDomain K k S) :
    IsAlternatingAnalyticDomain K k (fun X => S X ∨ universalTargetCore K k X) := by
  apply (isAlternatingAnalyticDomain_iff_coordinates K k _).2
  intro X Y hX hY
  rcases hX with hX | hX
  · rcases hY with hY | hY
    · exact (isAlternatingAnalyticDomain_iff_coordinates K k S).1 hS X Y hX hY
    · exact analyticOnNhd_alternatingMapAction_of_universal_target k (Or.inr hY)
  · exact analyticOnNhd_alternatingMapAction_of_universal_target k (Or.inl hX)

/-- Every incoming hom action with split destination is analytic; the source is arbitrary. -/
theorem alternatingFunctor_analyticOnNhd_hom_of_split_destination
    (X Y : (NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K) (hY : splitPairs K k Y) :
    AnalyticOnNhd K (fun f : X ⟶ Y => (alternatingFunctor K k).map f) Set.univ := by
  apply (analyticOnNhd_functorMapInCoordinates_iff (alternatingFunctor K k)
    (NormedSpaceCat.pairHomCoordinates X Y)
    (NormedSpaceCat.homCoordinates _ _)).1
  rw [alternatingFunctor_mapInCoordinates]
  exact analyticOnNhd_alternatingMapAction_of_split_destination k hY

theorem splitPairs_isAnalyticDomain :
    IsAlternatingAnalyticDomain K k (splitPairs K k) := by
  apply (isAlternatingAnalyticDomain_iff_coordinates K k _).2
  intro X Y _ hY
  exact analyticOnNhd_alternatingMapAction_of_split_destination k hY

/-- `dom:core`: core analyticity, the exact product characterization, compatibility
with every analytic domain, and closure under bounded retracts, bounded linear
isomorphisms, and all finite max-norm products, including the empty product. -/
theorem universalTarget_core :
    IsAlternatingAnalyticDomain K k (universalTargetCore K k) ∧
    (∀ T : ObjectProperty (NormedSpaceCat K),
      IsAlternatingAnalyticDomain K k (fun X => T X.2) ↔
        ∀ F, T F → UniversalAlternatingTarget K k F) ∧
    (∀ S : ObjectProperty ((NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K),
      IsAlternatingAnalyticDomain K k S →
        IsAlternatingAnalyticDomain K k (fun X => S X ∨ universalTargetCore K k X)) ∧
    (∀ (F G : Type u) [NormedAddCommGroup F] [NormedSpace K F]
      [NormedAddCommGroup G] [NormedSpace K G]
      (i : F →L[K] G) (r : G →L[K] F),
      r.comp i = ContinuousLinearMap.id K F →
        UniversalAlternatingTarget K k G → UniversalAlternatingTarget K k F) ∧
    (∀ (F G : Type u) [NormedAddCommGroup F] [NormedSpace K F]
      [NormedAddCommGroup G] [NormedSpace K G] (_e : F ≃L[K] G),
      UniversalAlternatingTarget K k F ↔ UniversalAlternatingTarget K k G) ∧
    (∀ (I : Type u) [Fintype I] (Fi : I → Type u)
      [∀ i, NormedAddCommGroup (Fi i)] [∀ i, NormedSpace K (Fi i)],
      (∀ i, UniversalAlternatingTarget K k (Fi i)) →
        UniversalAlternatingTarget K k (∀ i, Fi i)) := by
  refine ⟨universalTargetCore_isAnalyticDomain K k, product_isAnalyticDomain_iff K k,
    fun _ hS => hS.union_core K k, ?_, ?_, ?_⟩
  · intro F G _ _ _ _ i r hri hG
    exact hG.of_retract i r hri
  · intro F G _ _ _ _ e
    exact universalAlternatingTarget_iff_of_continuousLinearEquiv k e
  · intro I _ Fi _ _ h
    exact UniversalAlternatingTarget.pi h

/-- `dom:split-incoming`: analyticity of every actual incoming hom map to a split
destination and analytic-domain status of the full category of all split pairs. -/
theorem splitPairs_incoming_analytic :
    (∀ (X Y : (NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K), splitPairs K k Y →
      AnalyticOnNhd K (fun f : X ⟶ Y => (alternatingFunctor K k).map f) Set.univ) ∧
    IsAlternatingAnalyticDomain K k (splitPairs K k) :=
  ⟨alternatingFunctor_analyticOnNhd_hom_of_split_destination K k,
    splitPairs_isAnalyticDomain K k⟩

end AlternatingAnalytic
