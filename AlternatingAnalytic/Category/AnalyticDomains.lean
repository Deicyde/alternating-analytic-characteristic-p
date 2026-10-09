import AlternatingAnalytic.Category.AlternatingFunctor
import AlternatingAnalytic.Analysis.UniversalAlternatingTargets
import AlternatingAnalytic.Analysis.SplitAlternatingPairs

/-!
# Analytic domains: universal targets and split pairs

Defines analytic domains (Definition H.1): full subcategories of pairs `(op E, F)` on whose hom
spaces `Alt^k` is analytic, including homs between distinct objects. Hom spaces carry the max of
the two operator norms. Proves Lemma H.3 (split pairs form an analytic domain) and the basic
properties of the domain of pairs with a universal target (Section 9). All spaces and the field
lie in `Type u`.

## Main results

- `splitPairs_incoming_analytic`: Lemma H.3.
- `universalTarget_core`: the universal-target domain and its closure properties.
-/

noncomputable section

open CategoryTheory Opposite

universe u

namespace AlternatingAnalytic

variable (K : Type u) [NontriviallyNormedField K] (k : ℕ)

namespace NormedSpaceCat

variable {K}

/-- Operator coordinates of a hom in a full subcategory of pairs. The first operator goes
from the source space of `Y` to the source space of `X`. -/
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

/-- The inclusion of the full subcategory preserves operator coordinates. -/
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

/-- The restriction of `alternatingFunctor` to the full subcategory on `S`. -/
abbrev restrictedAlternatingFunctor
    (S : ObjectProperty ((NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K)) :=
  S.ι ⋙ alternatingFunctor K k

/-- In operator coordinates, the hom map of the restricted functor is `alternatingMapAction`. -/
theorem restrictedAlternatingFunctor_mapInCoordinates
    (S : ObjectProperty ((NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K))
    (X Y : S.FullSubcategory) :
    functorMapInCoordinates (restrictedAlternatingFunctor K k S)
      (NormedSpaceCat.restrictedPairHomCoordinates S X Y)
      (NormedSpaceCat.homCoordinates
        ((restrictedAlternatingFunctor K k S).obj X)
        ((restrictedAlternatingFunctor K k S).obj Y)) =
      alternatingMapAction k := rfl

/-- Definition H.1: `Alt^k` restricted to the full subcategory on `S` is analytic on every
hom space. -/
def IsAlternatingAnalyticDomain
    (S : ObjectProperty ((NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K)) : Prop :=
  FunctorAnalyticOnHoms K (S.ι ⋙ alternatingFunctor K k)

theorem isAlternatingAnalyticDomain_iff_functorAnalyticOnHoms
    (S : ObjectProperty ((NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K)) :
    IsAlternatingAnalyticDomain K k S ↔
      FunctorAnalyticOnHoms K (S.ι ⋙ alternatingFunctor K k) := Iff.rfl

/-- `S` is an analytic domain iff the action between any two objects of `S` is analytic. -/
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

/-- The property of being a universal alternating target in degree `k`. -/
def isUniversalAlternatingTarget : ObjectProperty (NormedSpaceCat K) :=
  fun F => UniversalAlternatingTarget K k F

/-- The full subcategory of universal alternating targets. -/
abbrev UniversalAlternatingTargetCat := (isUniversalAlternatingTarget K k).FullSubcategory

/-- The fully faithful inclusion of universal targets into normed spaces. -/
abbrev UniversalAlternatingTargetCat.inclusion :
    UniversalAlternatingTargetCat K k ⥤ NormedSpaceCat K :=
  (isUniversalAlternatingTarget K k).ι

/-- Pairs `(op E, F)` with `F` a universal target and `E` arbitrary. -/
def universalTargetCore : ObjectProperty ((NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K) :=
  fun X => UniversalAlternatingTarget K k X.2

abbrev UniversalTargetCoreCat := (universalTargetCore K k).FullSubcategory

/-- Definition H.2: pairs whose inclusion `Alt^k(E; F) → Mult^k(E; F)` has a bounded
retraction. -/
def splitPairs : ObjectProperty ((NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K) :=
  fun X => IsSplitAlternatingPair K k X.1.unop X.2

abbrev SplitAlternatingPairCat := (splitPairs K k).FullSubcategory

/-- A universal target at either endpoint makes the hom action analytic. -/
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

/-- A domain of the form `{(op E, F) | T F}` is analytic iff every `F` in `T` is a
universal target. -/
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

/-- Adjoining the universal-target pairs to an analytic domain keeps it analytic. -/
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

/-- Every hom action whose destination is a split pair is analytic. -/
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

/-- The universal-target pairs form an analytic domain, the largest of product form, and can be
adjoined to any analytic domain. Universal targets are closed under retracts, isomorphisms and
finite products. -/
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

/-- Lemma H.3: every hom action with split destination is analytic, so the split pairs form
an analytic domain. -/
theorem splitPairs_incoming_analytic :
    (∀ (X Y : (NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K), splitPairs K k Y →
      AnalyticOnNhd K (fun f : X ⟶ Y => (alternatingFunctor K k).map f) Set.univ) ∧
    IsAlternatingAnalyticDomain K k (splitPairs K k) :=
  ⟨alternatingFunctor_analyticOnNhd_hom_of_split_destination K k,
    splitPairs_isAnalyticDomain K k⟩

end AlternatingAnalytic
