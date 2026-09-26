import AlternatingAnalytic.Category.AnalyticDomainIsoClosure
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms

/-!
# Analytic domains relative to finite-dimensional ultrametric pairs

The ambient restriction retains the given norms. Isomorphism closure is taken
inside the restricted full category, so it cannot introduce a non-ultrametric norm.
-/

noncomputable section

open CategoryTheory Opposite

universe u

namespace AlternatingAnalytic

variable (K : Type u) [NontriviallyNormedField K] (k : ℕ)

/-- The actual finite-dimensional, nonarchimedean ambient object property. -/
def finiteUltrametricPairs :
    ObjectProperty ((NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K) :=
  fun X => FiniteDimensional K X.1.unop ∧ FiniteDimensional K X.2 ∧
    IsUltrametricDist X.1.unop ∧ IsUltrametricDist X.2

/-- The full category retaining the fixed ultrametric norms. -/
abbrev FiniteUltrametricPairCat := (finiteUltrametricPairs K).FullSubcategory

namespace NormedSpaceCat

variable {K}

/-- Coordinate equivalence after two actual full-subcategory restrictions. -/
def relativePairHomEquiv
    (Ω : ObjectProperty ((NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K))
    (S : ObjectProperty Ω.FullSubcategory) (X Y : S.FullSubcategory) :
    (X ⟶ Y) ≃ (Y.obj.obj.1.unop →L[K] X.obj.obj.1.unop) ×
      (X.obj.obj.2 →L[K] Y.obj.obj.2) :=
  InducedCategory.homEquiv.trans (restrictedPairHomEquiv Ω X.obj Y.obj)

instance relativePairHomNormedAddCommGroup
    (Ω : ObjectProperty ((NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K))
    (S : ObjectProperty Ω.FullSubcategory) (X Y : S.FullSubcategory) :
    NormedAddCommGroup (X ⟶ Y) :=
  (relativePairHomEquiv Ω S X Y).normedAddCommGroup

instance relativePairHomNormedSpace
    (Ω : ObjectProperty ((NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K))
    (S : ObjectProperty Ω.FullSubcategory) (X Y : S.FullSubcategory) :
    NormedSpace K (X ⟶ Y) where
  __ := (relativePairHomEquiv Ω S X Y).addEquiv.module K
  norm_smul_le c f := by
    change ‖c • relativePairHomEquiv Ω S X Y f‖ ≤
      ‖c‖ * ‖relativePairHomEquiv Ω S X Y f‖
    exact norm_smul_le c (relativePairHomEquiv Ω S X Y f)

/-- Canonical hom norms after both full restrictions. -/
def relativePairHomCoordinates
    (Ω : ObjectProperty ((NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K))
    (S : ObjectProperty Ω.FullSubcategory) (X Y : S.FullSubcategory) :
    (X ⟶ Y) ≃ₗᵢ[K] (Y.obj.obj.1.unop →L[K] X.obj.obj.1.unop) ×
      (X.obj.obj.2 →L[K] Y.obj.obj.2) where
  __ := (relativePairHomEquiv Ω S X Y).addEquiv.linearEquiv K
  norm_map' _ := rfl

end NormedSpaceCat

/-- Analyticity of the actual restricted functor in a prescribed full ambient category. -/
def IsRelativeAlternatingAnalyticDomain
    (Ω : ObjectProperty ((NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K))
    (S : ObjectProperty Ω.FullSubcategory) : Prop :=
  FunctorAnalyticOnHoms K (S.ι ⋙ Ω.ι ⋙ alternatingFunctor K k)

/-- Removing both full-subcategory wrappers gives the actual joint action. -/
theorem relativeAlternatingFunctor_mapInCoordinates
    (Ω : ObjectProperty ((NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K))
    (S : ObjectProperty Ω.FullSubcategory) (X Y : S.FullSubcategory) :
    functorMapInCoordinates (S.ι ⋙ Ω.ι ⋙ alternatingFunctor K k)
      (NormedSpaceCat.relativePairHomCoordinates Ω S X Y)
      (NormedSpaceCat.homCoordinates
        ((S.ι ⋙ Ω.ι ⋙ alternatingFunctor K k).obj X)
        ((S.ι ⋙ Ω.ι ⋙ alternatingFunctor K k).obj Y)) =
      alternatingMapAction k := rfl

theorem isRelativeAlternatingAnalyticDomain_iff_coordinates
    (Ω : ObjectProperty ((NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K))
    (S : ObjectProperty Ω.FullSubcategory) :
    IsRelativeAlternatingAnalyticDomain K k Ω S ↔
      ∀ (X Y : Ω.FullSubcategory), S X → S Y →
        AnalyticOnNhd K (alternatingMapAction (K := K)
          (E := X.obj.1.unop) (E' := Y.obj.1.unop)
          (F := X.obj.2) (F' := Y.obj.2) k) Set.univ := by
  unfold IsRelativeAlternatingAnalyticDomain
  rw [functorAnalyticOnHoms_iff_mapInCoordinates
    (e := NormedSpaceCat.relativePairHomCoordinates Ω S)
    (e' := fun _ _ => NormedSpaceCat.homCoordinates _ _)]
  simp only [relativeAlternatingFunctor_mapInCoordinates]
  constructor
  · intro h X Y hX hY
    exact h ⟨X, hX⟩ ⟨Y, hY⟩
  · intro h X Y
    exact h X.obj Y.obj X.property Y.property

/-- A singleton tests exactly its actual self-action, also in a restricted ambient category. -/
theorem isRelativeAlternatingAnalyticDomain_singleton_iff
    (Ω : ObjectProperty ((NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K))
    (X : Ω.FullSubcategory) :
    IsRelativeAlternatingAnalyticDomain K k Ω (fun Y => Y = X) ↔
      AnalyticOnNhd K (alternatingMapAction (K := K)
        (E := X.obj.1.unop) (E' := X.obj.1.unop)
        (F := X.obj.2) (F' := X.obj.2) k) Set.univ := by
  rw [isRelativeAlternatingAnalyticDomain_iff_coordinates]
  constructor
  · intro h
    exact h X X rfl rfl
  · rintro h Y Z rfl rfl
    exact h

/-- Two analytic singletons and one bad directed hom exclude a greatest full domain. -/
theorem no_greatest_relative_analytic_domain
    (Ω : ObjectProperty ((NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K))
    (X Y : Ω.FullSubcategory)
    (hX : AnalyticOnNhd K (alternatingMapAction (K := K)
      (E := X.obj.1.unop) (E' := X.obj.1.unop)
      (F := X.obj.2) (F' := X.obj.2) k) Set.univ)
    (hY : AnalyticOnNhd K (alternatingMapAction (K := K)
      (E := Y.obj.1.unop) (E' := Y.obj.1.unop)
      (F := Y.obj.2) (F' := Y.obj.2) k) Set.univ)
    (hYX : ¬AnalyticOnNhd K (alternatingMapAction (K := K)
      (E := Y.obj.1.unop) (E' := X.obj.1.unop)
      (F := Y.obj.2) (F' := X.obj.2) k) Set.univ) :
    ¬∃ S : ObjectProperty Ω.FullSubcategory,
      IsGreatest {P | IsRelativeAlternatingAnalyticDomain K k Ω P} S := by
  rintro ⟨S, hS, hmax⟩
  have hSX : S X := hmax
    ((isRelativeAlternatingAnalyticDomain_singleton_iff K k Ω X).2 hX) X rfl
  have hSY : S Y := hmax
    ((isRelativeAlternatingAnalyticDomain_singleton_iff K k Ω Y).2 hY) Y rfl
  exact hYX ((isRelativeAlternatingAnalyticDomain_iff_coordinates K k Ω S).1
    hS Y X hSY hSX)

/-- Taking isomorphism closure inside the restricted ambient category preserves
analyticity. No invariance of the ambient norm property is required. -/
theorem IsRelativeAlternatingAnalyticDomain.isoClosure
    (Ω : ObjectProperty ((NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K))
    {S : ObjectProperty Ω.FullSubcategory}
    (hS : IsRelativeAlternatingAnalyticDomain K k Ω S) :
    IsRelativeAlternatingAnalyticDomain K k Ω S.isoClosure := by
  apply (isRelativeAlternatingAnalyticDomain_iff_coordinates K k Ω _).2
  rintro X Y ⟨X₀, hX₀, ⟨e⟩⟩ ⟨Y₀, hY₀, ⟨f⟩⟩
  exact analyticOnNhd_alternatingMapAction_of_iso K k
    (Ω.ι.mapIso e) (Ω.ι.mapIso f)
    ((isRelativeAlternatingAnalyticDomain_iff_coordinates K k Ω S).1 hS
      X₀ Y₀ hX₀ hY₀)

/-- Two relative replete singleton domains exclude a greatest replete full domain.
Both closures below live in `Ω.FullSubcategory`. -/
theorem no_greatest_replete_relative_analytic_domain
    (Ω : ObjectProperty ((NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K))
    (X Y : Ω.FullSubcategory)
    (hX : AnalyticOnNhd K (alternatingMapAction (K := K)
      (E := X.obj.1.unop) (E' := X.obj.1.unop)
      (F := X.obj.2) (F' := X.obj.2) k) Set.univ)
    (hY : AnalyticOnNhd K (alternatingMapAction (K := K)
      (E := Y.obj.1.unop) (E' := Y.obj.1.unop)
      (F := Y.obj.2) (F' := Y.obj.2) k) Set.univ)
    (hYX : ¬AnalyticOnNhd K (alternatingMapAction (K := K)
      (E := Y.obj.1.unop) (E' := X.obj.1.unop)
      (F := Y.obj.2) (F' := X.obj.2) k) Set.univ) :
    ¬∃ S : ObjectProperty Ω.FullSubcategory,
      IsGreatest {P | IsRelativeAlternatingAnalyticDomain K k Ω P ∧
        P.IsClosedUnderIsomorphisms} S := by
  rintro ⟨S, ⟨hS, _⟩, hmax⟩
  let SX : ObjectProperty Ω.FullSubcategory := fun Z => Z = X
  let SY : ObjectProperty Ω.FullSubcategory := fun Z => Z = Y
  have hSX : IsRelativeAlternatingAnalyticDomain K k Ω SX.isoClosure :=
    ((isRelativeAlternatingAnalyticDomain_singleton_iff K k Ω X).2 hX).isoClosure K k Ω
  have hSY : IsRelativeAlternatingAnalyticDomain K k Ω SY.isoClosure :=
    ((isRelativeAlternatingAnalyticDomain_singleton_iff K k Ω Y).2 hY).isoClosure K k Ω
  have hXmem : S X := hmax ⟨hSX, inferInstance⟩ X (SX.le_isoClosure X rfl)
  have hYmem : S Y := hmax ⟨hSY, inferInstance⟩ Y (SY.le_isoClosure Y rfl)
  exact hYX ((isRelativeAlternatingAnalyticDomain_iff_coordinates K k Ω S).1
    hS Y X hYmem hXmem)

/-- Analytic full domains within the finite-dimensional ultrametric category. -/
abbrev IsFiniteUltrametricAnalyticDomain
    (S : ObjectProperty (FiniteUltrametricPairCat K)) : Prop :=
  IsRelativeAlternatingAnalyticDomain K k (finiteUltrametricPairs K) S

end AlternatingAnalytic
