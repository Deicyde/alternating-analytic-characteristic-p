import AlternatingAnalytic.Category.AlternatingFunctor
import AlternatingAnalytic.Analysis.AlternatingActionRegularity
import AlternatingAnalytic.Analysis.FactorialClassification
import AlternatingAnalytic.Analysis.PositiveCharacteristic

/-!
# Regularity of the functor Alt^k

The hom maps of `Alt^k` are C^∞, and they are analytic iff `k! ≠ 0` in `K`, on normed
and on Banach spaces (Corollary 6.2). With spherically complete targets over an ultrametric
field they are continuous polynomials in every degree (Theorem 4.2).

## Main results

- `alternatingFunctor_main`: Corollary 6.2 in functor form.
- `alternatingSphericalFunctor_main`: the spherical-target functor is a continuous polynomial.
- `alternatingSphericalFunctor_main_of_charP`: the same in characteristic `p`.
-/

noncomputable section

open CategoryTheory Opposite

universe u

namespace AlternatingAnalytic

variable (K : Type u) [NontriviallyNormedField K] (k : ℕ)

/-- Every hom map of `alternatingFunctor` is `C^n`. -/
theorem alternatingFunctor_contDiffOnHoms (n : ℕ∞) :
    FunctorContDiffOnHoms K n (alternatingFunctor K k) := by
  apply (functorContDiffOnHoms_iff_mapInCoordinates
    (A := alternatingFunctor K k) n NormedSpaceCat.pairHomCoordinates
    (fun _ _ => NormedSpaceCat.homCoordinates _ _)).2
  intro X Y
  rw [alternatingFunctor_mapInCoordinates]
  exact contDiff_alternatingMapAction k n

/-- Every hom map of `alternatingBanachFunctor` is `C^n`. -/
theorem alternatingBanachFunctor_contDiffOnHoms (n : ℕ∞) :
    FunctorContDiffOnHoms K n (alternatingBanachFunctor K k) := by
  apply (functorContDiffOnHoms_iff_mapInCoordinates
    (A := alternatingBanachFunctor K k) n (BanachCat.pairHomCoordinates K)
    (fun _ _ => BanachCat.homCoordinates K _ _)).2
  intro X Y
  rw [alternatingBanachFunctor_mapInCoordinates]
  exact contDiff_alternatingMapAction k n

/-- If `k! ≠ 0`, every hom map of `alternatingFunctor` is a continuous polynomial. -/
theorem alternatingFunctor_cpolynomialOnHoms (hk : (k.factorial : K) ≠ 0) :
    FunctorCPolynomialOnHoms K (alternatingFunctor K k) := by
  apply (functorCPolynomialOnHoms_iff_mapInCoordinates
    (A := alternatingFunctor K k) NormedSpaceCat.pairHomCoordinates
    (fun _ _ => NormedSpaceCat.homCoordinates _ _)).2
  intro X Y z
  rw [alternatingFunctor_mapInCoordinates]
  exact cpolynomialAt_alternatingMapAction_of_factorial_ne_zero k hk z

/-- If `k! ≠ 0`, every hom map of `alternatingBanachFunctor` is a continuous polynomial. -/
theorem alternatingBanachFunctor_cpolynomialOnHoms (hk : (k.factorial : K) ≠ 0) :
    FunctorCPolynomialOnHoms K (alternatingBanachFunctor K k) := by
  apply (functorCPolynomialOnHoms_iff_mapInCoordinates
    (A := alternatingBanachFunctor K k) (BanachCat.pairHomCoordinates K)
    (fun _ _ => BanachCat.homCoordinates K _ _)).2
  intro X Y z
  rw [alternatingBanachFunctor_mapInCoordinates]
  exact cpolynomialAt_alternatingMapAction_of_factorial_ne_zero k hk z

/-- `alternatingFunctor` is analytic on hom spaces iff `k! ≠ 0`. -/
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

/-- `alternatingBanachFunctor` is analytic on hom spaces iff `k! ≠ 0`. -/
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

/-- Corollary 6.2: `Alt^k` is C^∞ on hom spaces, analytic iff `k! ≠ 0`, and then a continuous
polynomial; on normed and on Banach spaces. -/
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

/-- With spherically complete targets, every hom map is a continuous polynomial.
The source spaces are arbitrary normed spaces. -/
theorem alternatingSphericalFunctor_cpolynomialOnHoms :
    FunctorCPolynomialOnHoms K (alternatingSphericalFunctor K k) := by
  apply (functorCPolynomialOnHoms_iff_mapInCoordinates
    (A := alternatingSphericalFunctor K k) (SphericalNormedSpaceCat.pairHomCoordinates K)
    (fun _ _ => SphericalNormedSpaceCat.homCoordinates K _ _)).2
  intro X Y z
  rw [alternatingSphericalFunctor_mapInCoordinates]
  exact cpolynomialAt_alternatingMapAction_of_sphericallyComplete k z

/-- With spherically complete targets, every hom map is analytic. -/
theorem alternatingSphericalFunctor_analyticOnHoms :
    FunctorAnalyticOnHoms K (alternatingSphericalFunctor K k) :=
  (alternatingSphericalFunctor_cpolynomialOnHoms K k).analyticOnHoms

/-- Over an ultrametric field, spherically complete targets give spherically complete
`Alt^k(E; F)` and hom maps that are continuous polynomials. -/
theorem alternatingSphericalFunctor_main :
    (∀ (E : NormedSpaceCat K) (F : SphericalNormedSpaceCat K),
      IsUltrametricDist (E [⋀^Fin k]→L[K] F) ∧
      SphericallyCompleteSpace (E [⋀^Fin k]→L[K] F)) ∧
    FunctorCPolynomialOnHoms K (alternatingSphericalFunctor K k) ∧
    FunctorAnalyticOnHoms K (alternatingSphericalFunctor K k) :=
  ⟨alternating_isSpherical K k, alternatingSphericalFunctor_cpolynomialOnHoms K k,
    alternatingSphericalFunctor_analyticOnHoms K k⟩

end Spherical

/-- `alternatingSphericalFunctor_main` in characteristic `p`, where `K` is automatically
ultrametric. -/
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
