import AlternatingAnalytic.Category.NormedSpace
import AlternatingAnalytic.Analysis.AnalyticFamilies
import AlternatingAnalytic.Analysis.AlternatingActionZero
import AlternatingAnalytic.Analysis.SphericalAnalytic

/-!
# Alternating bifunctors on normed, Banach, and spherical spaces

The first variable is contravariant: an arrow `(op E', F) ⟶ (op E, F')`
with coordinates `(u, v)` acts by `m ↦ v ∘ m ∘ (u, …, u)`.
The restrictions are obtained by composing with inclusions and then applying
`ObjectProperty.lift`. Completeness of the scalar field is never required.
-/

noncomputable section

open CategoryTheory Opposite

universe u

namespace AlternatingAnalytic

variable (K : Type u) [NontriviallyNormedField K] (k : ℕ)

/-- Pullback in the source and pushforward in the target of alternating maps. -/
def alternatingFunctor :
    (NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K ⥤ NormedSpaceCat K where
  obj X := NormedSpaceCat.of K (X.1.unop [⋀^Fin k]→L[K] X.2)
  map f := alternatingMapAction k (f.1.unop, f.2)
  map_id _X := alternatingMapAction_id k
  map_comp f g := alternatingMapAction_comp k (g.1.unop, g.2) (f.1.unop, f.2)

@[simp]
theorem alternatingFunctor_obj (E F : NormedSpaceCat K) :
    (alternatingFunctor K k).obj (op E, F) =
      NormedSpaceCat.of K (E [⋀^Fin k]→L[K] F) := rfl

/-- The input arrow goes from `(op E', F)` to `(op E, F')`. -/
@[simp]
theorem alternatingFunctor_map {E E' F F' : NormedSpaceCat K}
    (u : E →L[K] E') (v : F →L[K] F') :
    (alternatingFunctor K k).map
      (CategoryTheory.Prod.mkHom (Quiver.Hom.op (show E ⟶ E' from u)) v) =
        alternatingMapAction k (u, v) := rfl

@[simp]
theorem alternatingFunctor_map_apply {E E' F F' : NormedSpaceCat K}
    (u : E →L[K] E') (v : F →L[K] F')
    (m : E' [⋀^Fin k]→L[K] F) (x : Fin k → E) :
    (show (E' [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F') from
      (alternatingFunctor K k).map
        (CategoryTheory.Prod.mkHom (Quiver.Hom.op (show E ⟶ E' from u)) v)) m x =
        v (m (u ∘ x)) := rfl

/-- The actual hom map is exactly the checked joint action in operator coordinates. -/
theorem alternatingFunctor_mapInCoordinates
    (X Y : (NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K) :
    functorMapInCoordinates (alternatingFunctor K k)
      (NormedSpaceCat.pairHomCoordinates X Y)
      (NormedSpaceCat.homCoordinates
        ((alternatingFunctor K k).obj X) ((alternatingFunctor K k).obj Y)) =
      alternatingMapAction k := rfl

/-- Banach closure uses only completeness of the target. -/
theorem alternating_completeSpace (E F : NormedSpaceCat K) [CompleteSpace F] :
    CompleteSpace (E [⋀^Fin k]→L[K] F) := inferInstance

/-- Restrict both inputs to Banach spaces, then lift the output to Banach spaces. -/
def alternatingBanachFunctor : (BanachCat K)ᵒᵖ × BanachCat K ⥤ BanachCat K :=
  (isBanach K).lift
    (((BanachCat.inclusion K).op.prod (BanachCat.inclusion K)) ⋙ alternatingFunctor K k)
    (fun X => by
      change CompleteSpace (X.1.unop [⋀^Fin k]→L[K] X.2)
      infer_instance)

@[simp]
theorem alternatingBanachFunctor_obj (E F : BanachCat K) :
    (alternatingBanachFunctor K k).obj (op E, F) =
      BanachCat.of K (E [⋀^Fin k]→L[K] F) := rfl

/-- Forgetting the output restriction gives precisely the inclusion restriction. -/
theorem alternatingBanachFunctor_comp_inclusion :
    alternatingBanachFunctor K k ⋙ BanachCat.inclusion K =
      ((BanachCat.inclusion K).op.prod (BanachCat.inclusion K)) ⋙
        alternatingFunctor K k := rfl

@[simp]
theorem alternatingBanachFunctor_map {E E' F F' : BanachCat K}
    (u : E →L[K] E') (v : F →L[K] F') :
    ((alternatingBanachFunctor K k).map
      (CategoryTheory.Prod.mkHom
        (Quiver.Hom.op (ObjectProperty.homMk u : E ⟶ E'))
        (ObjectProperty.homMk v : F ⟶ F'))).hom =
      alternatingMapAction k (u, v) := rfl

@[simp]
theorem alternatingBanachFunctor_map_apply {E E' F F' : BanachCat K}
    (u : E →L[K] E') (v : F →L[K] F')
    (m : E' [⋀^Fin k]→L[K] F) (x : Fin k → E) :
    (show (E' [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F') from
      ((alternatingBanachFunctor K k).map
      (CategoryTheory.Prod.mkHom
        (Quiver.Hom.op (ObjectProperty.homMk u : E ⟶ E'))
        (ObjectProperty.homMk v : F ⟶ F'))).hom) m x =
      v (m (u ∘ x)) := rfl

theorem alternatingBanachFunctor_mapInCoordinates
    (X Y : (BanachCat K)ᵒᵖ × BanachCat K) :
    functorMapInCoordinates (alternatingBanachFunctor K k)
      (BanachCat.pairHomCoordinates K X Y)
      (BanachCat.homCoordinates K
        ((alternatingBanachFunctor K k).obj X) ((alternatingBanachFunctor K k).obj Y)) =
      alternatingMapAction k := rfl

section Spherical

variable [IsUltrametricDist K]

/-- Spherical closure places no completeness or ultrametric condition on `E`. -/
theorem alternating_isSpherical (E : NormedSpaceCat K) (F : SphericalNormedSpaceCat K) :
    IsUltrametricDist (E [⋀^Fin k]→L[K] F) ∧
      SphericallyCompleteSpace (E [⋀^Fin k]→L[K] F) :=
  ⟨inferInstance, inferInstance⟩

/-- Restrict only the second input, then lift the output to spherical spaces. -/
def alternatingSphericalFunctor :
    (NormedSpaceCat K)ᵒᵖ × SphericalNormedSpaceCat K ⥤ SphericalNormedSpaceCat K :=
  (isSpherical K).lift
    (((𝟭 (NormedSpaceCat K)ᵒᵖ).prod (SphericalNormedSpaceCat.inclusion K)) ⋙
      alternatingFunctor K k)
    (fun X => alternating_isSpherical K k X.1.unop X.2)

@[simp]
theorem alternatingSphericalFunctor_obj (E : NormedSpaceCat K)
    (F : SphericalNormedSpaceCat K) :
    (alternatingSphericalFunctor K k).obj (op E, F) =
      SphericalNormedSpaceCat.of K (E [⋀^Fin k]→L[K] F) := rfl

theorem alternatingSphericalFunctor_comp_inclusion :
    alternatingSphericalFunctor K k ⋙ SphericalNormedSpaceCat.inclusion K =
      ((𝟭 (NormedSpaceCat K)ᵒᵖ).prod (SphericalNormedSpaceCat.inclusion K)) ⋙
        alternatingFunctor K k := rfl

@[simp]
theorem alternatingSphericalFunctor_map {E E' : NormedSpaceCat K}
    {F F' : SphericalNormedSpaceCat K} (u : E →L[K] E') (v : F →L[K] F') :
    ((alternatingSphericalFunctor K k).map
      (CategoryTheory.Prod.mkHom (Quiver.Hom.op (show E ⟶ E' from u))
        (ObjectProperty.homMk v : F ⟶ F'))).hom =
      alternatingMapAction k (u, v) := rfl

@[simp]
theorem alternatingSphericalFunctor_map_apply {E E' : NormedSpaceCat K}
    {F F' : SphericalNormedSpaceCat K} (u : E →L[K] E') (v : F →L[K] F')
    (m : E' [⋀^Fin k]→L[K] F) (x : Fin k → E) :
    (show (E' [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F') from
      ((alternatingSphericalFunctor K k).map
      (CategoryTheory.Prod.mkHom (Quiver.Hom.op (show E ⟶ E' from u))
        (ObjectProperty.homMk v : F ⟶ F'))).hom) m x =
      v (m (u ∘ x)) := rfl

theorem alternatingSphericalFunctor_mapInCoordinates
    (X Y : (NormedSpaceCat K)ᵒᵖ × SphericalNormedSpaceCat K) :
    functorMapInCoordinates (alternatingSphericalFunctor K k)
      (SphericalNormedSpaceCat.pairHomCoordinates K X Y)
      (SphericalNormedSpaceCat.homCoordinates K
        ((alternatingSphericalFunctor K k).obj X)
        ((alternatingSphericalFunctor K k).obj Y)) =
      alternatingMapAction k := rfl

end Spherical

section DegreeZero

/-- The canonical isometric identification of the degree-zero object with its target. -/
def alternatingFunctorZeroCoordinates (E F : NormedSpaceCat K) :
    ((alternatingFunctor K 0).obj (op E, F)) ≃ₗᵢ[K] F :=
  (ContinuousAlternatingMap.constOfIsEmptyLIE K E F (Fin 0)).symm

/-- Under the degree-zero isometries, the actual functor map is `v`. -/
theorem alternatingFunctor_zero_map (X Y : (NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K)
    (z : (Y.1.unop →L[K] X.1.unop) × (X.2 →L[K] Y.2)) :
    ((ContinuousAlternatingMap.constOfIsEmptyLIE K Y.1.unop Y.2 (Fin 0)).symm :
      (Y.1.unop [⋀^Fin 0]→L[K] Y.2) →L[K] Y.2).comp
      ((functorMapInCoordinates (alternatingFunctor K 0)
          (NormedSpaceCat.pairHomCoordinates X Y)
          (NormedSpaceCat.homCoordinates
            ((alternatingFunctor K 0).obj X) ((alternatingFunctor K 0).obj Y)) z).comp
        (ContinuousAlternatingMap.constOfIsEmptyLIE K X.1.unop X.2 (Fin 0) :
          X.2 →L[K] (X.1.unop [⋀^Fin 0]→L[K] X.2))) = z.2 :=
  alternatingMapAction_zero_conjugate z.1 z.2

theorem alternatingBanachFunctor_zero_map (X Y : (BanachCat K)ᵒᵖ × BanachCat K)
    (z : (Y.1.unop →L[K] X.1.unop) × (X.2 →L[K] Y.2)) :
    ((ContinuousAlternatingMap.constOfIsEmptyLIE K Y.1.unop Y.2 (Fin 0)).symm :
      (Y.1.unop [⋀^Fin 0]→L[K] Y.2) →L[K] Y.2).comp
      ((functorMapInCoordinates (alternatingBanachFunctor K 0)
          (BanachCat.pairHomCoordinates K X Y)
          (BanachCat.homCoordinates K
            ((alternatingBanachFunctor K 0).obj X)
            ((alternatingBanachFunctor K 0).obj Y)) z).comp
        (ContinuousAlternatingMap.constOfIsEmptyLIE K X.1.unop X.2 (Fin 0) :
          X.2 →L[K] (X.1.unop [⋀^Fin 0]→L[K] X.2))) = z.2 :=
  alternatingMapAction_zero_conjugate z.1 z.2

theorem alternatingSphericalFunctor_zero_map [IsUltrametricDist K]
    (X Y : (NormedSpaceCat K)ᵒᵖ × SphericalNormedSpaceCat K)
    (z : (Y.1.unop →L[K] X.1.unop) × (X.2 →L[K] Y.2)) :
    ((ContinuousAlternatingMap.constOfIsEmptyLIE K Y.1.unop Y.2 (Fin 0)).symm :
      (Y.1.unop [⋀^Fin 0]→L[K] Y.2) →L[K] Y.2).comp
      ((functorMapInCoordinates (alternatingSphericalFunctor K 0)
          (SphericalNormedSpaceCat.pairHomCoordinates K X Y)
          (SphericalNormedSpaceCat.homCoordinates K
            ((alternatingSphericalFunctor K 0).obj X)
            ((alternatingSphericalFunctor K 0).obj Y)) z).comp
        (ContinuousAlternatingMap.constOfIsEmptyLIE K X.1.unop X.2 (Fin 0) :
          X.2 →L[K] (X.1.unop [⋀^Fin 0]→L[K] X.2))) = z.2 :=
  alternatingMapAction_zero_conjugate z.1 z.2

end DegreeZero

end AlternatingAnalytic
