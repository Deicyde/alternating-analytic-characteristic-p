import AlternatingAnalytic.Category.AnalyticDomains
import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms

/-!
# Isomorphism closure of full analytic domains

Composing with fixed isomorphisms at both ends preserves analyticity of a hom action of
`Alt^k`. Hence the isomorphism closure of an analytic domain (Definition H.1) is again an
analytic domain. This is used for the isomorphism-closed variant of Theorem H.4.
-/

noncomputable section

open CategoryTheory Opposite

universe u

namespace AlternatingAnalytic

variable (K : Type u) [NontriviallyNormedField K]

namespace NormedSpaceCat

variable {K}

/-- Precomposition and postcomposition by two fixed bounded maps. -/
def homSandwichCLM {E E' F F' : NormedSpaceCat K}
    (f : E' ⟶ E) (g : F ⟶ F') : (E ⟶ F) →L[K] (E' ⟶ F') :=
  (ContinuousLinearMap.compL K E' F F' g).comp
    ((ContinuousLinearMap.compL K E' E F).flip f)

@[simp]
theorem homSandwichCLM_apply {E E' F F' : NormedSpaceCat K}
    (f : E' ⟶ E) (g : F ⟶ F') (h : E ⟶ F) :
    homSandwichCLM f g h = f ≫ h ≫ g := rfl

/-- Composition with fixed arrows on both sides, as a bounded linear map on pair hom spaces. -/
def pairHomSandwichCLM
    {X X' Y Y' : (NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K}
    (f : X' ⟶ X) (g : Y ⟶ Y') : (X ⟶ Y) →L[K] (X' ⟶ Y') :=
  (pairHomCoordinates X' Y').symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (((homSandwichCLM g.1.unop f.1.unop).prodMap
      (homSandwichCLM f.2 g.2)).comp
        (pairHomCoordinates X Y).toContinuousLinearEquiv.toContinuousLinearMap)

@[simp]
theorem pairHomSandwichCLM_apply
    {X X' Y Y' : (NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K}
    (f : X' ⟶ X) (g : Y ⟶ Y') (h : X ⟶ Y) :
    pairHomSandwichCLM f g h = f ≫ h ≫ g := by
  apply (pairHomCoordinates X' Y').injective
  ext <;> rfl

end NormedSpaceCat

variable (k : ℕ)

/-- Analyticity of a hom action of `Alt^k` transports along isomorphisms of its endpoints. -/
theorem alternatingFunctor_analyticOnNhd_hom_of_iso
    {X Y X' Y' : (NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K}
    (e : X' ≅ X) (f : Y' ≅ Y)
    (h : AnalyticOnNhd K (fun a : X ⟶ Y => (alternatingFunctor K k).map a) Set.univ) :
    AnalyticOnNhd K (fun a : X' ⟶ Y' => (alternatingFunctor K k).map a) Set.univ := by
  let input := NormedSpaceCat.pairHomSandwichCLM e.inv f.hom
  let output := NormedSpaceCat.homSandwichCLM
    ((alternatingFunctor K k).map e.hom) ((alternatingFunctor K k).map f.inv)
  have heq : (fun a : X' ⟶ Y' => output ((alternatingFunctor K k).map (input a))) =
      (fun a : X' ⟶ Y' => (alternatingFunctor K k).map a) := by
    funext a
    simp only [input, output, NormedSpaceCat.homSandwichCLM_apply,
      NormedSpaceCat.pairHomSandwichCLM_apply, ← Functor.map_comp]
    congr 1
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  intro a _
  rw [← heq]
  exact (output.analyticAt _).comp
    ((h (input a) (Set.mem_univ _)).comp (input.analyticAt a))

/-- `alternatingFunctor_analyticOnNhd_hom_of_iso` in operator coordinates. -/
theorem analyticOnNhd_alternatingMapAction_of_iso
    {X Y X' Y' : (NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K}
    (e : X' ≅ X) (f : Y' ≅ Y)
    (h : AnalyticOnNhd K (alternatingMapAction (K := K)
      (E := X.1.unop) (E' := Y.1.unop) (F := X.2) (F' := Y.2) k) Set.univ) :
    AnalyticOnNhd K (alternatingMapAction (K := K)
      (E := X'.1.unop) (E' := Y'.1.unop) (F := X'.2) (F' := Y'.2) k) Set.univ := by
  have h' : AnalyticOnNhd K
      (fun a : X ⟶ Y => (alternatingFunctor K k).map a) Set.univ :=
    (analyticOnNhd_functorMapInCoordinates_iff (alternatingFunctor K k)
      (NormedSpaceCat.pairHomCoordinates X Y)
      (NormedSpaceCat.homCoordinates _ _)).1 h
  exact (analyticOnNhd_functorMapInCoordinates_iff (alternatingFunctor K k)
    (NormedSpaceCat.pairHomCoordinates X' Y')
    (NormedSpaceCat.homCoordinates _ _)).2
      (alternatingFunctor_analyticOnNhd_hom_of_iso K k e f h')

/-- The isomorphism closure of an analytic domain is an analytic domain. -/
theorem IsAlternatingAnalyticDomain.isoClosure
    {P : ObjectProperty ((NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K)}
    (hP : IsAlternatingAnalyticDomain K k P) :
    IsAlternatingAnalyticDomain K k P.isoClosure := by
  apply (isAlternatingAnalyticDomain_iff_coordinates K k _).2
  rintro X Y ⟨X₀, hX₀, ⟨e⟩⟩ ⟨Y₀, hY₀, ⟨f⟩⟩
  exact analyticOnNhd_alternatingMapAction_of_iso K k e f
    ((isAlternatingAnalyticDomain_iff_coordinates K k P).1 hP X₀ Y₀ hX₀ hY₀)

end AlternatingAnalytic
