import AlternatingAnalytic.Analysis.LaurentField
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Algebra.Field.ZMod
import AlternatingAnalytic.Analysis.LaurentSubfieldExtra.LaurentSubfieldClosure

/-!
# Lemma D.2 (Laurent subfield), p. 41

Solution: the statements of `Challenges/LemD_2.lean`, proved from the library
(`AlternatingAnalytic/Analysis/LaurentSubfieldExtra/`):
* (1): `AlternatingAnalytic.charP_isUltrametricDist_and_norm_zmod` (`LaurentPolynomialNorm.lean`);
* (2): `AlternatingAnalytic.norm_sum_zmod_zpow_eq` (`LaurentPolynomialNorm.lean`), the lowest
  term dominates by the ultrametric inequality;
* (3): `AlternatingAnalytic.exists_laurentField_evaluation` (`LaurentSubfieldClosure.lean`), from
  `exists_isometric_laurentField_embedding`, the Laurent expansion `hasSum_laurentSingle`
  (`LaurentExpansion.lean`) and `fieldRange_ratFunc_eq_subfieldClosure`;
* (4): `AlternatingAnalytic.sphericallyCompleteSpace_closure_subfieldClosure`
  (`LaurentSubfieldClosure.lean`), via `laurentField_range_properties`.
-/

open scoped NNReal

namespace AlternatingAnalyticChallenge.LemD_2

universe u

open AlternatingAnalytic

/-- **Lemma D.2(1).** A complete nontrivially normed field of characteristic `p` is
ultrametric, and every nonzero element of `𝔽_p` has absolute value `1` in it. -/
theorem part1
    (K' : Type u) [NontriviallyNormedField K'] [CompleteSpace K']
    (p : ℕ) [Fact p.Prime] [CharP K' p] :
    IsUltrametricDist K' ∧
      ∀ c : ZMod p, c ≠ 0 → ‖ZMod.castHom (dvd_refl p) K' c‖ = 1 := by
  exact AlternatingAnalytic.charP_isUltrametricDist_and_norm_zmod K' p

/-- **Lemma D.2(2).** A finite `𝔽_p`-combination `∑_{i=m}^{M} a_i t^i`, not all `a_i` zero,
has absolute value `‖t‖ ^ i₀`, where `i₀` is the least index with `a_{i₀} ≠ 0`. -/
theorem part2
    (K' : Type u) [NontriviallyNormedField K'] [CompleteSpace K']
    (p : ℕ) [Fact p.Prime] [CharP K' p]
    (t : K') (ht0 : 0 < ‖t‖) (ht1 : ‖t‖ < 1)
    (m M : ℤ) (a : ℤ → ZMod p) (i₀ : ℤ) (hi₀ : i₀ ∈ Finset.Icc m M) (ha : a i₀ ≠ 0)
    (hmin : ∀ i ∈ Finset.Icc m M, a i ≠ 0 → i₀ ≤ i) :
    ‖∑ i ∈ Finset.Icc m M, ZMod.castHom (dvd_refl p) K' (a i) * t ^ i‖ = ‖t‖ ^ i₀ := by
  exact AlternatingAnalytic.norm_sum_zmod_zpow_eq p t ht0 ht1 _ a i₀ hi₀ ha hmin

/-- **Lemma D.2(3).** For `‖t‖ = r ∈ (0, 1)` there is a continuous isometric ring
homomorphism `ev_t : 𝔽_p((X)) → K′` (with `|X| = r`) sending `∑ a_i X^i` to `∑ a_i t^i`;
its image is a closed subfield of `K′` equal to the closure of `𝔽_p(t)`. -/
theorem part3
    (K' : Type u) [NontriviallyNormedField K'] [CompleteSpace K']
    (p : ℕ) [Fact p.Prime] [CharP K' p]
    (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] (t : K') (ht : ‖t‖ = r) :
    ∃ ev : LaurentField (ZMod p) r →+* K',
      Continuous ev ∧ Isometry ev ∧
      (∀ x : LaurentField (ZMod p) r,
        HasSum (fun i : ℤ => ZMod.castHom (dvd_refl p) K' (LaurentField.coeff (ZMod p) r i x) *
          t ^ i) (ev x)) ∧
      IsClosed (ev.fieldRange : Set K') ∧
      (ev.fieldRange : Set K') = closure (Subfield.closure {t} : Set K') := by
  exact AlternatingAnalytic.exists_laurentField_evaluation p r t ht

/-- **Lemma D.2(4).** The closure `K₁` of `𝔽_p(t)` in `K′` is spherically complete. -/
theorem part4
    (K' : Type u) [NontriviallyNormedField K'] [CompleteSpace K']
    (p : ℕ) [Fact p.Prime] [CharP K' p]
    (t : K') (ht0 : 0 < ‖t‖) (ht1 : ‖t‖ < 1) :
    SphericallyCompleteSpace (closure (Subfield.closure {t} : Set K')) := by
  exact AlternatingAnalytic.sphericallyCompleteSpace_closure_subfieldClosure p t ht0 ht1

end AlternatingAnalyticChallenge.LemD_2
