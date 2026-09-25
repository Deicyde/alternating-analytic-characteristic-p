import AlternatingAnalytic.Category.AlternatingFunctor
import AlternatingAnalytic.Analysis.AlternatingActionRegularity
import AlternatingAnalytic.Analysis.FactorialClassification
import AlternatingAnalytic.Analysis.PositiveCharacteristic

/-!
# Regularity and classification of the alternating bifunctors

These are categorical statements about the actual functor maps, using their
canonical linear isometric hom coordinates. The converse uses the identity
pushforward slice and the universal Banach-space factorial classification.

`alternatingFunctor_main` collects Main Theorem (1), including the finite-power-
series strengthening. `alternatingSphericalFunctor_main` gives the stronger
ultrametric version of Main Theorem (2), and its positive-characteristic
specialization is `alternatingSphericalFunctor_main_of_charP`.
-/

noncomputable section

open CategoryTheory Opposite

universe u

namespace AlternatingAnalytic

variable (K : Type u) [NontriviallyNormedField K] (k : ℕ)

/-- Every joint hom map of the normed-space alternating bifunctor is smooth. -/
theorem alternatingFunctor_contDiffOnHoms (n : ℕ∞) :
    FunctorContDiffOnHoms K n (alternatingFunctor K k) := by
  apply (functorContDiffOnHoms_iff_mapInCoordinates
    (A := alternatingFunctor K k) n NormedSpaceCat.pairHomCoordinates
    (fun _ _ => NormedSpaceCat.homCoordinates _ _)).2
  intro X Y
  rw [alternatingFunctor_mapInCoordinates]
  exact contDiff_alternatingMapAction k n

/-- Banach closure imposes no completeness assumption on the field. -/
theorem alternatingBanachFunctor_contDiffOnHoms (n : ℕ∞) :
    FunctorContDiffOnHoms K n (alternatingBanachFunctor K k) := by
  apply (functorContDiffOnHoms_iff_mapInCoordinates
    (A := alternatingBanachFunctor K k) n (BanachCat.pairHomCoordinates K)
    (fun _ _ => BanachCat.homCoordinates K _ _)).2
  intro X Y
  rw [alternatingBanachFunctor_mapInCoordinates]
  exact contDiff_alternatingMapAction k n

/-- Nonvanishing factorial gives finite power series on every joint Vec hom map. -/
theorem alternatingFunctor_cpolynomialOnHoms (hk : (k.factorial : K) ≠ 0) :
    FunctorCPolynomialOnHoms K (alternatingFunctor K k) := by
  apply (functorCPolynomialOnHoms_iff_mapInCoordinates
    (A := alternatingFunctor K k) NormedSpaceCat.pairHomCoordinates
    (fun _ _ => NormedSpaceCat.homCoordinates _ _)).2
  intro X Y z
  rw [alternatingFunctor_mapInCoordinates]
  exact cpolynomialAt_alternatingMapAction_of_factorial_ne_zero k hk z

/-- The finite-power-series conclusion also holds on the actual Banach hom maps. -/
theorem alternatingBanachFunctor_cpolynomialOnHoms (hk : (k.factorial : K) ≠ 0) :
    FunctorCPolynomialOnHoms K (alternatingBanachFunctor K k) := by
  apply (functorCPolynomialOnHoms_iff_mapInCoordinates
    (A := alternatingBanachFunctor K k) (BanachCat.pairHomCoordinates K)
    (fun _ _ => BanachCat.homCoordinates K _ _)).2
  intro X Y z
  rw [alternatingBanachFunctor_mapInCoordinates]
  exact cpolynomialAt_alternatingMapAction_of_factorial_ne_zero k hk z

/-- Exact analyticity classification of the normed-space bifunctor. -/
theorem alternatingFunctor_analyticOnHoms_iff :
    FunctorAnalyticOnHoms K (alternatingFunctor K k) ↔ (k.factorial : K) ≠ 0 := by
  constructor
  · intro h
    apply (factorial_ne_zero_iff_allBanachPrecompositionAnalytic K k).2
    intro E E' F _ _ _ _ _ _ _ _ _ u₀
    apply analyticAt_precomposition_of_analyticAt_alternatingMapAction k u₀
    let X : (NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K :=
      (op (NormedSpaceCat.of K E'), NormedSpaceCat.of K F)
    let Y : (NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K :=
      (op (NormedSpaceCat.of K E), NormedSpaceCat.of K F)
    have hcoord := (analyticOnNhd_functorMapInCoordinates_iff (alternatingFunctor K k)
      (NormedSpaceCat.pairHomCoordinates X Y)
      (NormedSpaceCat.homCoordinates _ _)).2 (h X Y)
    rw [alternatingFunctor_mapInCoordinates] at hcoord
    exact hcoord (u₀, ContinuousLinearMap.id K F) (Set.mem_univ _)
  · intro hk
    exact (alternatingFunctor_cpolynomialOnHoms K k hk).analyticOnHoms

/-- Exact analyticity classification on the full Banach subcategories. -/
theorem alternatingBanachFunctor_analyticOnHoms_iff :
    FunctorAnalyticOnHoms K (alternatingBanachFunctor K k) ↔ (k.factorial : K) ≠ 0 := by
  constructor
  · intro h
    apply (factorial_ne_zero_iff_allBanachPrecompositionAnalytic K k).2
    intro E E' F _ _ _ _ _ _ _ _ _ u₀
    apply analyticAt_precomposition_of_analyticAt_alternatingMapAction k u₀
    let X : (BanachCat K)ᵒᵖ × BanachCat K :=
      (op (BanachCat.of K E'), BanachCat.of K F)
    let Y : (BanachCat K)ᵒᵖ × BanachCat K :=
      (op (BanachCat.of K E), BanachCat.of K F)
    have hcoord := (analyticOnNhd_functorMapInCoordinates_iff
      (alternatingBanachFunctor K k) (BanachCat.pairHomCoordinates K X Y)
      (BanachCat.homCoordinates K _ _)).2 (h X Y)
    rw [alternatingBanachFunctor_mapInCoordinates] at hcoord
    exact hcoord (u₀, ContinuousLinearMap.id K F) (Set.mem_univ _)
  · intro hk
    exact (alternatingBanachFunctor_cpolynomialOnHoms K k hk).analyticOnHoms

/-- Main Theorem (1): universal smoothness, both exact analytic classifications,
and finite power series in the analytic range, in every degree including zero. -/
theorem alternatingFunctor_main :
    (∀ n : ℕ∞, FunctorContDiffOnHoms K n (alternatingFunctor K k)) ∧
    (∀ n : ℕ∞, FunctorContDiffOnHoms K n (alternatingBanachFunctor K k)) ∧
    (FunctorAnalyticOnHoms K (alternatingFunctor K k) ↔ (k.factorial : K) ≠ 0) ∧
    (FunctorAnalyticOnHoms K (alternatingBanachFunctor K k) ↔ (k.factorial : K) ≠ 0) ∧
    ((k.factorial : K) ≠ 0 →
      FunctorCPolynomialOnHoms K (alternatingFunctor K k) ∧
      FunctorCPolynomialOnHoms K (alternatingBanachFunctor K k)) :=
  ⟨alternatingFunctor_contDiffOnHoms K k, alternatingBanachFunctor_contDiffOnHoms K k,
    alternatingFunctor_analyticOnHoms_iff K k, alternatingBanachFunctor_analyticOnHoms_iff K k,
    fun hk => ⟨alternatingFunctor_cpolynomialOnHoms K k hk,
      alternatingBanachFunctor_cpolynomialOnHoms K k hk⟩⟩

section Spherical

variable [IsUltrametricDist K]

/-- Spherical targets give finite power series for joint hom maps in every degree.
The contravariant source spaces are arbitrary normed spaces. -/
theorem alternatingSphericalFunctor_cpolynomialOnHoms :
    FunctorCPolynomialOnHoms K (alternatingSphericalFunctor K k) := by
  apply (functorCPolynomialOnHoms_iff_mapInCoordinates
    (A := alternatingSphericalFunctor K k) (SphericalNormedSpaceCat.pairHomCoordinates K)
    (fun _ _ => SphericalNormedSpaceCat.homCoordinates K _ _)).2
  intro X Y z
  rw [alternatingSphericalFunctor_mapInCoordinates]
  exact cpolynomialAt_alternatingMapAction_of_sphericallyComplete k z

/-- The spherical bifunctor is jointly analytic in every degree. -/
theorem alternatingSphericalFunctor_analyticOnHoms :
    FunctorAnalyticOnHoms K (alternatingSphericalFunctor K k) :=
  (alternatingSphericalFunctor_cpolynomialOnHoms K k).analyticOnHoms

/-- Main Theorem (2), strengthened to every ultrametric base field and finite
power series. The functor's codomain includes spherical closure. -/
theorem alternatingSphericalFunctor_main :
    (∀ (E : NormedSpaceCat K) (F : SphericalNormedSpaceCat K),
      IsUltrametricDist (E [⋀^Fin k]→L[K] F) ∧
      SphericallyCompleteSpace (E [⋀^Fin k]→L[K] F)) ∧
    FunctorCPolynomialOnHoms K (alternatingSphericalFunctor K k) ∧
    FunctorAnalyticOnHoms K (alternatingSphericalFunctor K k) :=
  ⟨alternating_isSpherical K k, alternatingSphericalFunctor_cpolynomialOnHoms K k,
    alternatingSphericalFunctor_analyticOnHoms K k⟩

end Spherical

/-- The manuscript's positive-characteristic specialization of Main Theorem (2).
No completeness assumption on the field is introduced. -/
theorem alternatingSphericalFunctor_main_of_charP (p : ℕ) [Fact p.Prime] [CharP K p] :
    letI : IsUltrametricDist K := charP_isUltrametricDist p
    (∀ (E : NormedSpaceCat K) (F : SphericalNormedSpaceCat K),
      IsUltrametricDist (E [⋀^Fin k]→L[K] F) ∧
      SphericallyCompleteSpace (E [⋀^Fin k]→L[K] F)) ∧
    FunctorCPolynomialOnHoms K (alternatingSphericalFunctor K k) ∧
    FunctorAnalyticOnHoms K (alternatingSphericalFunctor K k) := by
  let : IsUltrametricDist K := charP_isUltrametricDist p
  exact alternatingSphericalFunctor_main K k

end AlternatingAnalytic
