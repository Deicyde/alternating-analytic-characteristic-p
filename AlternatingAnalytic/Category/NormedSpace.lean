import AlternatingAnalytic.Analysis.SphericalCompleteness
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Module.TransferInstance
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Products.Basic

/-!
# Categories of normed spaces and their hom spaces

Defines `Vec_K` (`NormedSpaceCat`: normed spaces and bounded linear maps, as in the
Introduction) and its full subcategories `BanachCat` and `SphericalNormedSpaceCat`
(`Vec_K°`: ultrametric and spherically complete). Hom spaces carry the operator norm, products
the max norm, and the first coordinate of a hom in `Vec_Kᵒᵖ × Vec_K` is reversed. All spaces and
the field lie in one universe.

`FunctorContDiffOnHoms`, `FunctorAnalyticOnHoms` and `FunctorCPolynomialOnHoms` say that every
hom map of a functor is `C^n`, analytic, or a continuous polynomial. Each can be checked in any
linear isometric coordinates on the hom spaces.
-/

noncomputable section

open CategoryTheory Opposite

universe u

namespace AlternatingAnalytic

variable (K : Type u) [NontriviallyNormedField K]

/-- Normed `K`-spaces, with no completeness assumption. -/
structure NormedSpaceCat where
  carrier : Type u
  [normedAddCommGroup : NormedAddCommGroup carrier]
  [normedSpace : NormedSpace K carrier]

attribute [instance] NormedSpaceCat.normedAddCommGroup NormedSpaceCat.normedSpace

namespace NormedSpaceCat

instance : CoeSort (NormedSpaceCat K) (Type u) := ⟨carrier⟩

/-- Bundle a normed space as an object. -/
abbrev of (E : Type u) [NormedAddCommGroup E] [NormedSpace K E] : NormedSpaceCat K :=
  ⟨E⟩

instance : Category (NormedSpaceCat K) where
  Hom E F := E →L[K] F
  id E := ContinuousLinearMap.id K E
  comp f g := g.comp f
  id_comp f := ContinuousLinearMap.comp_id f
  comp_id f := ContinuousLinearMap.id_comp f
  assoc f g h := (ContinuousLinearMap.comp_assoc h g f).symm

instance : ConcreteCategory (NormedSpaceCat K) (· →L[K] ·) where
  hom f := f
  ofHom f := f

variable {K}

instance (E F : NormedSpaceCat K) : NormedAddCommGroup (E ⟶ F) :=
  inferInstanceAs (NormedAddCommGroup (E →L[K] F))

instance (E F : NormedSpaceCat K) : NormedSpace K (E ⟶ F) :=
  inferInstanceAs (NormedSpace K (E →L[K] F))

/-- Canonical operator-norm coordinates on a hom space. -/
def homCoordinates (E F : NormedSpaceCat K) : (E ⟶ F) ≃ₗᵢ[K] (E →L[K] F) :=
  LinearIsometryEquiv.refl K _

@[simp]
theorem homCoordinates_apply {E F : NormedSpaceCat K} (f : E ⟶ F) :
    homCoordinates E F f = f := rfl

@[simp]
theorem homCoordinates_id (E : NormedSpaceCat K) :
    homCoordinates E E (𝟙 E) = ContinuousLinearMap.id K E := rfl

@[simp]
theorem homCoordinates_comp {E F G : NormedSpaceCat K} (f : E ⟶ F) (g : F ⟶ G) :
    homCoordinates E G (f ≫ g) = (homCoordinates F G g).comp (homCoordinates E F f) := rfl

/-- The canonical equivalence for any full subcategory of normed spaces. -/
def fullHomEquiv (P : ObjectProperty (NormedSpaceCat K)) (E F : P.FullSubcategory) :
    (E ⟶ F) ≃ (E.obj →L[K] F.obj) :=
  InducedCategory.homEquiv

instance fullHomNormedAddCommGroup (P : ObjectProperty (NormedSpaceCat K))
    (E F : P.FullSubcategory) : NormedAddCommGroup (E ⟶ F) :=
  (fullHomEquiv P E F).normedAddCommGroup

instance fullHomNormedSpace (P : ObjectProperty (NormedSpaceCat K))
    (E F : P.FullSubcategory) : NormedSpace K (E ⟶ F) where
  __ := (fullHomEquiv P E F).addEquiv.module K
  norm_smul_le c f := by
    change ‖c • (fullHomEquiv P E F f)‖ ≤ ‖c‖ * ‖fullHomEquiv P E F f‖
    exact norm_smul_le c (fullHomEquiv P E F f)

/-- Homs in a full subcategory, as a linear isometry with bounded linear maps. -/
def fullHomCoordinates (P : ObjectProperty (NormedSpaceCat K)) (E F : P.FullSubcategory) :
    (E ⟶ F) ≃ₗᵢ[K] (E.obj →L[K] F.obj) where
  __ := (fullHomEquiv P E F).addEquiv.linearEquiv K
  norm_map' _ := rfl

@[simp]
theorem fullHomCoordinates_apply (P : ObjectProperty (NormedSpaceCat K))
    {E F : P.FullSubcategory} (f : E ⟶ F) : fullHomCoordinates P E F f = f.hom := rfl

@[simp]
theorem fullHomCoordinates_id (P : ObjectProperty (NormedSpaceCat K))
    (E : P.FullSubcategory) :
    fullHomCoordinates P E E (𝟙 E) = ContinuousLinearMap.id K E.obj := rfl

@[simp]
theorem fullHomCoordinates_comp (P : ObjectProperty (NormedSpaceCat K))
    {E F G : P.FullSubcategory} (f : E ⟶ F) (g : F ⟶ G) :
    fullHomCoordinates P E G (f ≫ g) =
      (fullHomCoordinates P F G g).comp (fullHomCoordinates P E F f) := rfl

@[simp]
theorem fullHomCoordinates_symm_apply (P : ObjectProperty (NormedSpaceCat K))
    (E F : P.FullSubcategory) (f : E.obj →L[K] F.obj) :
    (fullHomCoordinates P E F).symm f = ObjectProperty.homMk f := rfl

/-- The inclusion of a full subcategory is the identity in operator coordinates. -/
theorem fullHomCoordinates_inclusion (P : ObjectProperty (NormedSpaceCat K))
    {E F : P.FullSubcategory} (f : E ⟶ F) :
    homCoordinates E.obj F.obj (P.ι.map f) = fullHomCoordinates P E F f := rfl

section Opposite

variable {C : Type*} [Category C]
  [∀ X Y : C, NormedAddCommGroup (X ⟶ Y)] [∀ X Y : C, NormedSpace K (X ⟶ Y)]

instance opHomNormedAddCommGroup (X Y : Cᵒᵖ) : NormedAddCommGroup (X ⟶ Y) :=
  (CategoryTheory.opEquiv X Y).normedAddCommGroup

instance opHomNormedSpace (X Y : Cᵒᵖ) : NormedSpace K (X ⟶ Y) where
  __ := (CategoryTheory.opEquiv X Y).addEquiv.module K
  norm_smul_le a f := by
    change ‖(CategoryTheory.opEquiv X Y)
      ((CategoryTheory.opEquiv X Y).symm (a • (CategoryTheory.opEquiv X Y) f))‖ ≤
      ‖a‖ * ‖(CategoryTheory.opEquiv X Y) f‖
    simpa only [Equiv.apply_symm_apply] using
      (norm_smul_le a ((CategoryTheory.opEquiv X Y) f))

/-- Homs in `Cᵒᵖ`, as a linear isometry with homs in `C`. -/
def opHomCoordinates (X Y : Cᵒᵖ) : (X ⟶ Y) ≃ₗᵢ[K] (Y.unop ⟶ X.unop) where
  toLinearEquiv := (CategoryTheory.opEquiv X Y).addEquiv.linearEquiv K
  norm_map' _ := rfl

@[simp]
theorem opHomCoordinates_apply (X Y : Cᵒᵖ) (f : X ⟶ Y) :
    opHomCoordinates (K := K) X Y f = f.unop := rfl

@[simp]
theorem opHomCoordinates_symm_apply (X Y : Cᵒᵖ) (f : Y.unop ⟶ X.unop) :
    (opHomCoordinates (K := K) X Y).symm f = f.op := rfl

end Opposite

section Product

variable {C D : Type*} [Category C] [Category D]
  [∀ X Y : C, NormedAddCommGroup (X ⟶ Y)] [∀ X Y : C, NormedSpace K (X ⟶ Y)]
  [∀ X Y : D, NormedAddCommGroup (X ⟶ Y)] [∀ X Y : D, NormedSpace K (X ⟶ Y)]

instance prodHomNormedAddCommGroup (X Y : C × D) : NormedAddCommGroup (X ⟶ Y) :=
  inferInstanceAs (NormedAddCommGroup ((X.1 ⟶ Y.1) × (X.2 ⟶ Y.2)))

instance prodHomNormedSpace (X Y : C × D) : NormedSpace K (X ⟶ Y) :=
  inferInstanceAs (NormedSpace K ((X.1 ⟶ Y.1) × (X.2 ⟶ Y.2)))

end Product

/-- Coordinates on homs of `Vec_Kᵒᵖ × Vec_K`, with the max norm. -/
def pairHomCoordinates (X Y : (NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K) :
    (X ⟶ Y) ≃ₗᵢ[K] (Y.1.unop →L[K] X.1.unop) × (X.2 →L[K] Y.2) where
  toLinearEquiv := (opHomCoordinates X.1 Y.1).toLinearEquiv.prodCongr
    (homCoordinates X.2 Y.2).toLinearEquiv
  norm_map' _ := rfl

@[simp]
theorem pairHomCoordinates_apply {X Y : (NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K}
    (f : X ⟶ Y) : pairHomCoordinates X Y f = (f.1.unop, f.2) := rfl

@[simp]
theorem pairHomCoordinates_symm_apply (X Y : (NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K)
    (f : (Y.1.unop →L[K] X.1.unop) × (X.2 →L[K] Y.2)) :
    (pairHomCoordinates X Y).symm f =
      (Quiver.Hom.op (show Y.1.unop ⟶ X.1.unop from f.1), f.2) := rfl

theorem norm_pair_hom {X Y : (NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K} (f : X ⟶ Y) :
    ‖f‖ = max ‖(pairHomCoordinates X Y f).1‖ ‖(pairHomCoordinates X Y f).2‖ := rfl

@[simp]
theorem pairHomCoordinates_id (X : (NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K) :
    pairHomCoordinates X X (𝟙 X) =
      (ContinuousLinearMap.id K X.1.unop, ContinuousLinearMap.id K X.2) := rfl

@[simp]
theorem pairHomCoordinates_comp {X Y Z : (NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    pairHomCoordinates X Z (f ≫ g) =
      ((pairHomCoordinates X Y f).1.comp (pairHomCoordinates Y Z g).1,
        (pairHomCoordinates Y Z g).2.comp (pairHomCoordinates X Y f).2) := rfl

/-- `pairHomCoordinates` for full subcategories in each factor. -/
def fullPairHomCoordinates (P Q : ObjectProperty (NormedSpaceCat K))
    (X Y : P.FullSubcategoryᵒᵖ × Q.FullSubcategory) :
    (X ⟶ Y) ≃ₗᵢ[K]
      (Y.1.unop.obj →L[K] X.1.unop.obj) × (X.2.obj →L[K] Y.2.obj) where
  toLinearEquiv :=
    ((opHomCoordinates X.1 Y.1).trans
      (fullHomCoordinates P Y.1.unop X.1.unop)).toLinearEquiv.prodCongr
        (fullHomCoordinates Q X.2 Y.2).toLinearEquiv
  norm_map' _ := rfl

@[simp]
theorem fullPairHomCoordinates_apply (P Q : ObjectProperty (NormedSpaceCat K))
    {X Y : P.FullSubcategoryᵒᵖ × Q.FullSubcategory} (f : X ⟶ Y) :
    fullPairHomCoordinates P Q X Y f = (f.1.unop.hom, f.2.hom) := rfl

@[simp]
theorem fullPairHomCoordinates_id (P Q : ObjectProperty (NormedSpaceCat K))
    (X : P.FullSubcategoryᵒᵖ × Q.FullSubcategory) :
    fullPairHomCoordinates P Q X X (𝟙 X) =
      (ContinuousLinearMap.id K X.1.unop.obj, ContinuousLinearMap.id K X.2.obj) := rfl

@[simp]
theorem fullPairHomCoordinates_comp (P Q : ObjectProperty (NormedSpaceCat K))
    {X Y Z : P.FullSubcategoryᵒᵖ × Q.FullSubcategory} (f : X ⟶ Y) (g : Y ⟶ Z) :
    fullPairHomCoordinates P Q X Z (f ≫ g) =
      ((fullPairHomCoordinates P Q X Y f).1.comp (fullPairHomCoordinates P Q Y Z g).1,
        (fullPairHomCoordinates P Q Y Z g).2.comp (fullPairHomCoordinates P Q X Y f).2) := rfl

end NormedSpaceCat

/-- The complete objects of the normed-space category. -/
def isBanach : ObjectProperty (NormedSpaceCat K) := fun E => CompleteSpace E

/-- The full subcategory of Banach spaces. The field need not be complete. -/
abbrev BanachCat := (isBanach K).FullSubcategory

/-- Another name for the full subcategory of complete normed spaces. -/
abbrev BanachSpaceCat := BanachCat K

/-- The nonarchimedean, spherically complete objects. -/
def isSpherical : ObjectProperty (NormedSpaceCat K) :=
  fun E => IsUltrametricDist E ∧ SphericallyCompleteSpace E

/-- The full subcategory `Vec_K°` of spherically complete targets (Theorem 4.2). -/
abbrev SphericalNormedSpaceCat := (isSpherical K).FullSubcategory

namespace BanachCat

instance : CoeSort (BanachCat K) (Type u) := ⟨fun E => E.obj⟩
instance (E : BanachCat K) : NormedAddCommGroup E := E.obj.normedAddCommGroup
instance (E : BanachCat K) : NormedSpace K E := E.obj.normedSpace
instance (E : BanachCat K) : CompleteSpace E := E.property

/-- Bundle a complete normed space. -/
abbrev of (E : Type u) [NormedAddCommGroup E] [NormedSpace K E] [CompleteSpace E] :
    BanachCat K := ⟨NormedSpaceCat.of K E, ‹CompleteSpace E›⟩

/-- The fully faithful inclusion into normed spaces. -/
abbrev inclusion : BanachCat K ⥤ NormedSpaceCat K := (isBanach K).ι

/-- Hom coordinates in `BanachCat`, with the operator norm. -/
abbrev homCoordinates (E F : BanachCat K) : (E ⟶ F) ≃ₗᵢ[K] (E →L[K] F) :=
  NormedSpaceCat.fullHomCoordinates (isBanach K) E F

/-- Hom coordinates in `BanachCatᵒᵖ × BanachCat`. -/
abbrev pairHomCoordinates (X Y : (BanachCat K)ᵒᵖ × BanachCat K) :
    (X ⟶ Y) ≃ₗᵢ[K] (Y.1.unop →L[K] X.1.unop) × (X.2 →L[K] Y.2) :=
  NormedSpaceCat.fullPairHomCoordinates (isBanach K) (isBanach K) X Y

end BanachCat

namespace SphericalNormedSpaceCat

instance : CoeSort (SphericalNormedSpaceCat K) (Type u) := ⟨fun E => E.obj⟩
instance (E : SphericalNormedSpaceCat K) : NormedAddCommGroup E := E.obj.normedAddCommGroup
instance (E : SphericalNormedSpaceCat K) : NormedSpace K E := E.obj.normedSpace
instance (E : SphericalNormedSpaceCat K) : IsUltrametricDist E := E.property.1
instance (E : SphericalNormedSpaceCat K) : SphericallyCompleteSpace E := E.property.2

/-- Bundle an ultrametric, spherically complete normed space. -/
abbrev of (E : Type u) [NormedAddCommGroup E] [NormedSpace K E]
    [IsUltrametricDist E] [SphericallyCompleteSpace E] : SphericalNormedSpaceCat K :=
  ⟨NormedSpaceCat.of K E, inferInstance, inferInstance⟩

/-- The fully faithful inclusion into normed spaces. -/
abbrev inclusion : SphericalNormedSpaceCat K ⥤ NormedSpaceCat K := (isSpherical K).ι

/-- Hom coordinates in `SphericalNormedSpaceCat`, with the operator norm. -/
abbrev homCoordinates (E F : SphericalNormedSpaceCat K) : (E ⟶ F) ≃ₗᵢ[K] (E →L[K] F) :=
  NormedSpaceCat.fullHomCoordinates (isSpherical K) E F

/-- Coordinates for `Vec_Kᵒᵖ × Vec_K°`; the source is an arbitrary normed space. -/
def pairHomCoordinates (X Y : (NormedSpaceCat K)ᵒᵖ × SphericalNormedSpaceCat K) :
    (X ⟶ Y) ≃ₗᵢ[K] (Y.1.unop →L[K] X.1.unop) × (X.2 →L[K] Y.2) where
  toLinearEquiv := (NormedSpaceCat.opHomCoordinates X.1 Y.1).toLinearEquiv.prodCongr
    (homCoordinates K X.2 Y.2).toLinearEquiv
  norm_map' _ := rfl

@[simp]
theorem pairHomCoordinates_apply
    {X Y : (NormedSpaceCat K)ᵒᵖ × SphericalNormedSpaceCat K} (f : X ⟶ Y) :
    pairHomCoordinates K X Y f = (f.1.unop, f.2.hom) := rfl

@[simp]
theorem pairHomCoordinates_id (X : (NormedSpaceCat K)ᵒᵖ × SphericalNormedSpaceCat K) :
    pairHomCoordinates K X X (𝟙 X) =
      (ContinuousLinearMap.id K X.1.unop, ContinuousLinearMap.id K X.2) := rfl

@[simp]
theorem pairHomCoordinates_comp
    {X Y Z : (NormedSpaceCat K)ᵒᵖ × SphericalNormedSpaceCat K} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pairHomCoordinates K X Z (f ≫ g) =
      ((pairHomCoordinates K X Y f).1.comp (pairHomCoordinates K Y Z g).1,
        (pairHomCoordinates K Y Z g).2.comp (pairHomCoordinates K X Y f).2) := rfl

end SphericalNormedSpaceCat

section HomRegularity

variable {C D : Type*} [Category C] [Category D]
  [∀ X Y : C, NormedAddCommGroup (X ⟶ Y)] [∀ X Y : C, NormedSpace K (X ⟶ Y)]
  [∀ X Y : D, NormedAddCommGroup (X ⟶ Y)] [∀ X Y : D, NormedSpace K (X ⟶ Y)]

/-- Every hom map of `A` is `C^n`. Here `n : ℕ∞`, so `n = ∞` is allowed but `ω` is not. -/
def FunctorContDiffOnHoms (n : ℕ∞) (A : C ⥤ D) : Prop :=
  ∀ X Y : C, ContDiff K n (fun f : X ⟶ Y => A.map f)

/-- Every hom map of `A` is analytic at every point. -/
def FunctorAnalyticOnHoms (A : C ⥤ D) : Prop :=
  ∀ X Y : C, AnalyticOnNhd K (fun f : X ⟶ Y => A.map f) Set.univ

/-- Every hom map of `A` is a continuous polynomial near every point. -/
def FunctorCPolynomialOnHoms (A : C ⥤ D) : Prop :=
  ∀ (X Y : C) (f : X ⟶ Y), CPolynomialAt K (fun g : X ⟶ Y => A.map g) f

variable {K}

theorem functorContDiffOnHoms_iff (n : ℕ∞) (A : C ⥤ D) :
    FunctorContDiffOnHoms K n A ↔
      ∀ X Y : C, ContDiff K n (fun f : X ⟶ Y => A.map f) := Iff.rfl

theorem functorAnalyticOnHoms_iff (A : C ⥤ D) :
    FunctorAnalyticOnHoms K A ↔
      ∀ X Y : C, AnalyticOnNhd K (fun f : X ⟶ Y => A.map f) Set.univ := Iff.rfl

theorem functorCPolynomialOnHoms_iff (A : C ⥤ D) :
    FunctorCPolynomialOnHoms K A ↔
      ∀ (X Y : C) (f : X ⟶ Y), CPolynomialAt K (fun g : X ⟶ Y => A.map g) f := Iff.rfl

theorem functorAnalyticOnHoms_iff_analyticAt (A : C ⥤ D) :
    FunctorAnalyticOnHoms K A ↔
      ∀ (X Y : C) (f : X ⟶ Y), AnalyticAt K (fun g : X ⟶ Y => A.map g) f := by
  simp only [FunctorAnalyticOnHoms, AnalyticOnNhd, Set.mem_univ, forall_true_left]

/-- Continuous polynomial hom maps are analytic. -/
theorem FunctorCPolynomialOnHoms.analyticOnHoms {A : C ⥤ D}
    (h : FunctorCPolynomialOnHoms K A) : FunctorAnalyticOnHoms K A :=
  fun X Y f _ => (h X Y f).analyticAt

variable (A : C ⥤ D) {X Y : C}
  {H H' : Type*} [NormedAddCommGroup H] [NormedSpace K H]
  [NormedAddCommGroup H'] [NormedSpace K H']

/-- The hom map of `A` in chosen linear isometric coordinates. -/
def functorMapInCoordinates (e : (X ⟶ Y) ≃ₗᵢ[K] H)
    (e' : (A.obj X ⟶ A.obj Y) ≃ₗᵢ[K] H') : H → H' :=
  fun f => e' (A.map (e.symm f))

@[simp]
theorem functorMapInCoordinates_apply (e : (X ⟶ Y) ≃ₗᵢ[K] H)
    (e' : (A.obj X ⟶ A.obj Y) ≃ₗᵢ[K] H') (f : H) :
    functorMapInCoordinates A e e' f = e' (A.map (e.symm f)) := rfl

/-- In coordinates, an arrow is sent to the coordinates of its image. -/
@[simp]
theorem functorMapInCoordinates_apply_coordinates (e : (X ⟶ Y) ≃ₗᵢ[K] H)
    (e' : (A.obj X ⟶ A.obj Y) ≃ₗᵢ[K] H') (f : X ⟶ Y) :
    functorMapInCoordinates A e e' (e f) = e' (A.map f) := by
  simp only [functorMapInCoordinates, LinearIsometryEquiv.symm_apply_apply]

/-- Undoing the coordinates recovers `A.map`. -/
theorem functorMapInCoordinates_eq_map (e : (X ⟶ Y) ≃ₗᵢ[K] H)
    (e' : (A.obj X ⟶ A.obj Y) ≃ₗᵢ[K] H') (f : X ⟶ Y) :
    e'.symm (functorMapInCoordinates A e e' (e f)) = A.map f := by
  simp only [functorMapInCoordinates_apply_coordinates, LinearIsometryEquiv.symm_apply_apply]

/-- Smoothness of a hom map is equivalent to smoothness in isometric coordinates. -/
theorem contDiff_functorMapInCoordinates_iff (n : ℕ∞) (e : (X ⟶ Y) ≃ₗᵢ[K] H)
    (e' : (A.obj X ⟶ A.obj Y) ≃ₗᵢ[K] H') :
    ContDiff K n (functorMapInCoordinates A e e') ↔
      ContDiff K n (fun f : X ⟶ Y => A.map f) := by
  change ContDiff K n
    (e'.toContinuousLinearEquiv ∘ ((fun f : X ⟶ Y => A.map f) ∘
      e.symm.toContinuousLinearEquiv)) ↔ _
  rw [e'.toContinuousLinearEquiv.comp_contDiff_iff,
    e.symm.toContinuousLinearEquiv.contDiff_comp_iff]

/-- Pointwise analyticity can be checked in isometric hom coordinates. -/
theorem analyticAt_functorMapInCoordinates_iff (e : (X ⟶ Y) ≃ₗᵢ[K] H)
    (e' : (A.obj X ⟶ A.obj Y) ≃ₗᵢ[K] H') (f : X ⟶ Y) :
    AnalyticAt K (functorMapInCoordinates A e e') (e f) ↔
      AnalyticAt K (fun g : X ⟶ Y => A.map g) f := by
  change AnalyticAt K (fun z => e' (A.map (e.symm z))) (e f) ↔ _
  constructor
  · intro h
    have h' := (e'.symm.analyticAt _).comp (h.comp (e.analyticAt f))
    simpa only [functorMapInCoordinates, Function.comp_def,
      LinearIsometryEquiv.symm_apply_apply] using h'
  · intro h
    have h' := (e'.analyticAt _).comp
      (h.comp_of_eq (e.symm.analyticAt (e f)) (e.symm_apply_apply f))
    simpa only [functorMapInCoordinates, Function.comp_def] using h'

/-- Finite continuous power series are preserved and reflected by hom coordinates. -/
theorem cpolynomialAt_functorMapInCoordinates_iff (e : (X ⟶ Y) ≃ₗᵢ[K] H)
    (e' : (A.obj X ⟶ A.obj Y) ≃ₗᵢ[K] H') (f : X ⟶ Y) :
    CPolynomialAt K (functorMapInCoordinates A e e') (e f) ↔
      CPolynomialAt K (fun g : X ⟶ Y => A.map g) f := by
  change CPolynomialAt K (fun z => e' (A.map (e.symm z))) (e f) ↔ _
  constructor
  · intro h
    have h' := (e'.symm.toContinuousLinearEquiv.toContinuousLinearMap.cpolynomialAt _).comp
      (h.comp (e.toContinuousLinearEquiv.toContinuousLinearMap.cpolynomialAt f))
    simpa only [functorMapInCoordinates, Function.comp_def, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      LinearIsometryEquiv.symm_apply_apply] using h'
  · intro h
    have h' := (e'.toContinuousLinearEquiv.toContinuousLinearMap.cpolynomialAt _).comp
      (h.comp_of_eq (e.symm.toContinuousLinearEquiv.toContinuousLinearMap.cpolynomialAt (e f))
        (e.symm_apply_apply f))
    simpa only [functorMapInCoordinates, Function.comp_def, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv] using h'

/-- Global analyticity is independent of the chosen isometric hom coordinates. -/
theorem analyticOnNhd_functorMapInCoordinates_iff (e : (X ⟶ Y) ≃ₗᵢ[K] H)
    (e' : (A.obj X ⟶ A.obj Y) ≃ₗᵢ[K] H') :
    AnalyticOnNhd K (functorMapInCoordinates A e e') Set.univ ↔
      AnalyticOnNhd K (fun f : X ⟶ Y => A.map f) Set.univ := by
  constructor
  · intro h f _
    exact (analyticAt_functorMapInCoordinates_iff A e e' f).1 (h (e f) (Set.mem_univ _))
  · intro h f _
    have h' := (analyticAt_functorMapInCoordinates_iff A e e' (e.symm f)).2
      (h (e.symm f) (Set.mem_univ _))
    simpa only [LinearIsometryEquiv.apply_symm_apply] using h'

variable {V W : C → C → Type*}
  [∀ X Y, NormedAddCommGroup (V X Y)] [∀ X Y, NormedSpace K (V X Y)]
  [∀ X Y, NormedAddCommGroup (W X Y)] [∀ X Y, NormedSpace K (W X Y)]

/-- `FunctorContDiffOnHoms` can be checked in any isometric hom coordinates. -/
theorem functorContDiffOnHoms_iff_mapInCoordinates (n : ℕ∞)
    (e : ∀ X Y, (X ⟶ Y) ≃ₗᵢ[K] V X Y)
    (e' : ∀ X Y, (A.obj X ⟶ A.obj Y) ≃ₗᵢ[K] W X Y) :
    FunctorContDiffOnHoms K n A ↔
      ∀ X Y, ContDiff K n (functorMapInCoordinates A (e X Y) (e' X Y)) := by
  simp only [FunctorContDiffOnHoms, contDiff_functorMapInCoordinates_iff]

/-- `FunctorAnalyticOnHoms` can be checked in any isometric hom coordinates. -/
theorem functorAnalyticOnHoms_iff_mapInCoordinates
    (e : ∀ X Y, (X ⟶ Y) ≃ₗᵢ[K] V X Y)
    (e' : ∀ X Y, (A.obj X ⟶ A.obj Y) ≃ₗᵢ[K] W X Y) :
    FunctorAnalyticOnHoms K A ↔
      ∀ X Y, AnalyticOnNhd K (functorMapInCoordinates A (e X Y) (e' X Y)) Set.univ := by
  simp only [FunctorAnalyticOnHoms, analyticOnNhd_functorMapInCoordinates_iff]

/-- `FunctorCPolynomialOnHoms` can be checked in any isometric hom coordinates. -/
theorem functorCPolynomialOnHoms_iff_mapInCoordinates
    (e : ∀ X Y, (X ⟶ Y) ≃ₗᵢ[K] V X Y)
    (e' : ∀ X Y, (A.obj X ⟶ A.obj Y) ≃ₗᵢ[K] W X Y) :
    FunctorCPolynomialOnHoms K A ↔
      ∀ (X Y : C) (f : V X Y),
        CPolynomialAt K (functorMapInCoordinates A (e X Y) (e' X Y)) f := by
  constructor
  · intro h X Y f
    have h' := (cpolynomialAt_functorMapInCoordinates_iff A (e X Y) (e' X Y)
      ((e X Y).symm f)).2 (h X Y ((e X Y).symm f))
    simpa only [LinearIsometryEquiv.apply_symm_apply] using h'
  · intro h X Y f
    exact (cpolynomialAt_functorMapInCoordinates_iff A (e X Y) (e' X Y) f).1
      (h X Y (e X Y f))

end HomRegularity

end AlternatingAnalytic
