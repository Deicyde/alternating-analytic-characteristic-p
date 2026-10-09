import AlternatingAnalytic.Geometry.AnalyticBundleCategory
import AlternatingAnalytic.Geometry.AnalyticAlternatingBundleMorphism
import Mathlib.CategoryTheory.Products.Basic

/-!
# The alternating bifunctor on analytic bundles

Over an analytic manifold whose model has finite continuous coordinates, fiberwise
alternating maps give a functor `(AnalyticBundleCat)ᵒᵖ × AnalyticBundleCat ⥤
AnalyticBundleCat`. The objects keep Mathlib's fibers, total-space topology and atlas.
This is the bifunctor of Corollary 4.6 in the finite-coordinate setting.
-/

noncomputable section

open Bundle CategoryTheory Opposite
open scoped Bundle Manifold ContDiff

universe u

namespace AlternatingAnalytic

variable {K P M : Type u} [NontriviallyNormedField K]
  [NormedAddCommGroup P] [NormedSpace K P]
  [TopologicalSpace M] [ChartedSpace P M] [IsManifold 𝓘(K, P) ω M]
  {d : ℕ} (c : P ≃L[K] (Fin d → K)) (k : ℕ)

/-- The alternating bundle of two analytic bundles, with Mathlib's topology and atlas. -/
def alternatingBundleObj (X Y : AnalyticBundleCat 𝓘(K, P) M) :
    AnalyticBundleCat 𝓘(K, P) M := by
  letI := contMDiffVectorBundle_alternating_of_finiteCoordinates
    (F₁ := X.Model) (E₁ := X.Fiber) (F₂ := Y.Model) (E₂ := Y.Fiber) c k
  exact AnalyticBundleCat.of 𝓘(K, P) M (X.Model [⋀^Fin k]→L[K] Y.Model)
    (fun b ↦ X.Fiber b [⋀^Fin k]→L[K] Y.Fiber b)

/-- The alternating bundle bifunctor. -/
def alternatingBundleFunctor :
    (AnalyticBundleCat 𝓘(K, P) M)ᵒᵖ × AnalyticBundleCat 𝓘(K, P) M ⥤
      AnalyticBundleCat 𝓘(K, P) M where
  obj X := alternatingBundleObj c k X.1.unop X.2
  map a := alternatingBundleHom_of_finiteCoordinates c k a.1.unop a.2
  map_id X := by
    apply AnalyticBundleCat.hom_ext (X := alternatingBundleObj c k X.1.unop X.2)
      (Y := alternatingBundleObj c k X.1.unop X.2)
    intro b
    change alternatingBundleMap k ((𝟙 X.1).unop b) ((𝟙 X.2) b) = _
    rw [CategoryTheory.unop_id, AnalyticBundleCat.id_apply, AnalyticBundleCat.id_apply,
      AnalyticBundleCat.id_apply]
    exact alternatingBundleMap_id k
  map_comp {X Y Z} a a' := by
    apply AnalyticBundleCat.hom_ext (X := alternatingBundleObj c k X.1.unop X.2)
      (Y := alternatingBundleObj c k Z.1.unop Z.2)
    intro b
    change alternatingBundleMap k ((a.1 ≫ a'.1).unop b) ((a.2 ≫ a'.2) b) = _
    rw [CategoryTheory.unop_comp, AnalyticBundleCat.comp_apply,
      AnalyticBundleCat.comp_apply]
    exact alternatingBundleMap_comp k (a.1.unop b) (a'.1.unop b) (a.2 b) (a'.2 b)

/-- The model fiber is the space of continuous alternating maps between the models. -/
@[simp]
theorem alternatingBundleFunctor_obj_model (X Y : AnalyticBundleCat 𝓘(K, P) M) :
    ((alternatingBundleFunctor c k).obj (op X, Y)).Model =
      (X.Model [⋀^Fin k]→L[K] Y.Model) := rfl

/-- The fibers are the spaces of continuous alternating maps between the fibers. -/
@[simp]
theorem alternatingBundleFunctor_obj_fiber (X Y : AnalyticBundleCat 𝓘(K, P) M) (b : M) :
    ((alternatingBundleFunctor c k).obj (op X, Y)).Fiber b =
      (X.Fiber b [⋀^Fin k]→L[K] Y.Fiber b) := rfl

/-- The fibers carry the topology of continuous alternating maps. -/
theorem alternatingBundleFunctor_obj_fiberTopology
    (X Y : AnalyticBundleCat 𝓘(K, P) M) (b : M) :
    ((alternatingBundleFunctor c k).obj (op X, Y)).fiberTopology b =
      ContinuousAlternatingMap.instTopologicalSpace
        (𝕜 := K) (ι := Fin k) (E := X.Fiber b) (F := Y.Fiber b) := rfl

/-- The total-space topology is Mathlib's. -/
theorem alternatingBundleFunctor_obj_totalSpaceTopology
    (X Y : AnalyticBundleCat 𝓘(K, P) M) :
    ((alternatingBundleFunctor c k).obj (op X, Y)).totalSpaceTopology =
      Bundle.ContinuousAlternatingMap.instTopologicalSpaceTotalSpace
        (𝕜 := K) (ι := Fin k) (F₁ := X.Model) (E₁ := X.Fiber)
        (F₂ := Y.Model) (E₂ := Y.Fiber) := rfl

/-- The fiber bundle structure is Mathlib's alternating bundle atlas. -/
theorem alternatingBundleFunctor_obj_fiberBundle
    (X Y : AnalyticBundleCat 𝓘(K, P) M) :
    ((alternatingBundleFunctor c k).obj (op X, Y)).fiberBundle =
      Bundle.ContinuousAlternatingMap.instFiberBundle
        (𝕜 := K) (ι := Fin k) (F₁ := X.Model) (E₁ := X.Fiber)
        (F₂ := Y.Model) (E₂ := Y.Fiber) := rfl

/-- The vector bundle structure is Mathlib's. -/
theorem alternatingBundleFunctor_obj_vectorBundle
    (X Y : AnalyticBundleCat 𝓘(K, P) M) :
    ((alternatingBundleFunctor c k).obj (op X, Y)).vectorBundle =
      Bundle.ContinuousAlternatingMap.instVectorBundle
        (𝕜 := K) (ι := Fin k) (F₁ := X.Model) (E₁ := X.Fiber)
        (F₂ := Y.Model) (E₂ := Y.Fiber) := rfl

/-- On each fiber, the functor acts by `alternatingBundleMap`. -/
@[simp]
theorem alternatingBundleFunctor_map_apply
    {X Y : (AnalyticBundleCat 𝓘(K, P) M)ᵒᵖ × AnalyticBundleCat 𝓘(K, P) M}
    (a : X ⟶ Y) (b : M) :
    (alternatingBundleFunctor c k).map a b =
      alternatingBundleMap k (a.1.unop b) (a.2 b) := rfl

/-- On each fiber, a morphism acts by pullback in every input and postcomposition. -/
theorem alternatingBundleFunctor_map_apply_apply
    {X Y : (AnalyticBundleCat 𝓘(K, P) M)ᵒᵖ × AnalyticBundleCat 𝓘(K, P) M}
    (a : X ⟶ Y) (b : M) (m : X.1.unop.Fiber b [⋀^Fin k]→L[K] X.2.Fiber b) :
    (alternatingBundleFunctor c k).map a b m =
      (a.2 b).compContinuousAlternatingMap (m.compContinuousLinearMap (a.1.unop b)) :=
  alternatingBundleHom_of_finiteCoordinates_apply_apply c k a.1.unop a.2 b m

/-- The model, fibers and morphism action of the alternating bundle functor. -/
theorem alternatingBundleFunctor_spec :
    (∀ X Y : AnalyticBundleCat 𝓘(K, P) M,
      ((alternatingBundleFunctor c k).obj (op X, Y)).Model =
        (X.Model [⋀^Fin k]→L[K] Y.Model)) ∧
    (∀ (X Y : AnalyticBundleCat 𝓘(K, P) M) (b : M),
      ((alternatingBundleFunctor c k).obj (op X, Y)).Fiber b =
        (X.Fiber b [⋀^Fin k]→L[K] Y.Fiber b)) ∧
    (∀ (X Y : (AnalyticBundleCat 𝓘(K, P) M)ᵒᵖ × AnalyticBundleCat 𝓘(K, P) M)
      (a : X ⟶ Y) (b : M) (m : X.1.unop.Fiber b [⋀^Fin k]→L[K] X.2.Fiber b),
      (alternatingBundleFunctor c k).map a b m =
        (a.2 b).compContinuousAlternatingMap
          (m.compContinuousLinearMap (a.1.unop b))) :=
  ⟨alternatingBundleFunctor_obj_model c k, alternatingBundleFunctor_obj_fiber c k,
    fun _ _ a b m ↦ alternatingBundleFunctor_map_apply_apply c k a b m⟩

/-- Isomorphic analytic presentations induce isomorphic alternating bundles. -/
def alternatingBundleIso {X X' Y Y' : AnalyticBundleCat 𝓘(K, P) M}
    (eX : X ≅ X') (eY : Y ≅ Y') :
    (alternatingBundleFunctor c k).obj (op X, Y) ≅
      (alternatingBundleFunctor c k).obj (op X', Y') :=
  (alternatingBundleFunctor c k).mapIso (eX.symm.op.prod eY)

@[simp]
theorem alternatingBundleIso_hom_apply
    {X X' Y Y' : AnalyticBundleCat 𝓘(K, P) M}
    (eX : X ≅ X') (eY : Y ≅ Y') (b : M)
    (m : X.Fiber b [⋀^Fin k]→L[K] Y.Fiber b) :
    (alternatingBundleIso c k eX eY).hom b m =
      (eY.hom b).compContinuousAlternatingMap (m.compContinuousLinearMap (eX.inv b)) :=
  rfl

@[simp]
theorem alternatingBundleIso_inv_apply
    {X X' Y Y' : AnalyticBundleCat 𝓘(K, P) M}
    (eX : X ≅ X') (eY : Y ≅ Y') (b : M)
    (m : X'.Fiber b [⋀^Fin k]→L[K] Y'.Fiber b) :
    (alternatingBundleIso c k eX eY).inv b m =
      (eY.inv b).compContinuousAlternatingMap (m.compContinuousLinearMap (eX.hom b)) :=
  rfl

section CompatiblePresentations

variable {X X' Y Y' : AnalyticBundleCat 𝓘(K, P) M}
  (eX : ∀ b, X.Fiber b ≃L[K] X'.Fiber b)
  (eY : ∀ b, Y.Fiber b ≃L[K] Y'.Fiber b)
  (hX : AnalyticBundleCat.OperatorAnalytic (X := X) (Y := X')
    (fun b ↦ (eX b).toContinuousLinearMap))
  (hX' : AnalyticBundleCat.OperatorAnalytic (X := X') (Y := X)
    (fun b ↦ (eX b).symm.toContinuousLinearMap))
  (hY : AnalyticBundleCat.OperatorAnalytic (X := Y) (Y := Y')
    (fun b ↦ (eY b).toContinuousLinearMap))
  (hY' : AnalyticBundleCat.OperatorAnalytic (X := Y') (Y := Y)
    (fun b ↦ (eY b).symm.toContinuousLinearMap))

/-- Fiberwise equivalences that are analytic in both directions induce an isomorphism
of alternating bundles. With identity equivalences, this covers a compatible change of
model or atlas. -/
def alternatingBundlePresentationIso :
    (alternatingBundleFunctor c k).obj (op X, Y) ≅
      (alternatingBundleFunctor c k).obj (op X', Y') :=
  alternatingBundleIso c k
    (AnalyticBundleCat.isoOfOperatorAnalytic eX hX hX')
    (AnalyticBundleCat.isoOfOperatorAnalytic eY hY hY')

@[simp]
theorem alternatingBundlePresentationIso_hom_apply (b : M)
    (m : X.Fiber b [⋀^Fin k]→L[K] Y.Fiber b) :
    (alternatingBundlePresentationIso c k eX eY hX hX' hY hY').hom b m =
      (eY b).toContinuousLinearMap.compContinuousAlternatingMap
        (m.compContinuousLinearMap (eX b).symm.toContinuousLinearMap) := rfl

@[simp]
theorem alternatingBundlePresentationIso_inv_apply (b : M)
    (m : X'.Fiber b [⋀^Fin k]→L[K] Y'.Fiber b) :
    (alternatingBundlePresentationIso c k eX eY hX hX' hY hY').inv b m =
      (eY b).symm.toContinuousLinearMap.compContinuousAlternatingMap
        (m.compContinuousLinearMap (eX b).toContinuousLinearMap) := rfl

end CompatiblePresentations

end AlternatingAnalytic
