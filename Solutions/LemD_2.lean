import AlternatingAnalytic.Analysis.LaurentField
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Algebra.Field.ZMod
import AlternatingAnalytic.Analysis.LaurentSubfieldExtra.LaurentSubfieldClosure

/-!
# Proof of Lemma D.2

Uses `charP_isUltrametricDist_and_norm_zmod` and `norm_sum_zmod_zpow_eq`
(`LaurentPolynomialNorm.lean`), `exists_laurentField_evaluation` and
`sphericallyCompleteSpace_closure_subfieldClosure` (`LaurentSubfieldClosure.lean`), all in
`AlternatingAnalytic/Analysis/LaurentSubfieldExtra/`.
-/

open scoped NNReal

namespace AlternatingAnalyticChallenge.LemD_2

universe u

open AlternatingAnalytic

/-- A complete nontrivially normed field of characteristic `p` is ultrametric, and
nonzero elements of `𝔽_p` have norm `1` in it. -/
theorem part1
    (K' : Type u) [NontriviallyNormedField K'] [CompleteSpace K']
    (p : ℕ) [Fact p.Prime] [CharP K' p] :
    IsUltrametricDist K' ∧
      ∀ c : ZMod p, c ≠ 0 → ‖ZMod.castHom (dvd_refl p) K' c‖ = 1 := by
  exact AlternatingAnalytic.charP_isUltrametricDist_and_norm_zmod K' p

/-- A sum `∑_{i=m}^{M} a_i t^i` with not all `a_i` zero has norm `‖t‖ ^ i₀`, where `i₀` is
the least index with `a_{i₀} ≠ 0`. -/
theorem part2
    (K' : Type u) [NontriviallyNormedField K'] [CompleteSpace K']
    (p : ℕ) [Fact p.Prime] [CharP K' p]
    (t : K') (ht0 : 0 < ‖t‖) (ht1 : ‖t‖ < 1)
    (m M : ℤ) (a : ℤ → ZMod p) (i₀ : ℤ) (hi₀ : i₀ ∈ Finset.Icc m M) (ha : a i₀ ≠ 0)
    (hmin : ∀ i ∈ Finset.Icc m M, a i ≠ 0 → i₀ ≤ i) :
    ‖∑ i ∈ Finset.Icc m M, ZMod.castHom (dvd_refl p) K' (a i) * t ^ i‖ = ‖t‖ ^ i₀ := by
  exact AlternatingAnalytic.norm_sum_zmod_zpow_eq p t ht0 ht1 _ a i₀ hi₀ ha hmin

/-- Evaluation at `t` is a continuous isometric ring homomorphism `𝔽_p((X)) → K′`, with
`|X| = ‖t‖`, whose image is closed and equals the closure of `𝔽_p(t)`. -/
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

/-- The closure of `𝔽_p(t)` in `K′` is spherically complete. -/
theorem part4
    (K' : Type u) [NontriviallyNormedField K'] [CompleteSpace K']
    (p : ℕ) [Fact p.Prime] [CharP K' p]
    (t : K') (ht0 : 0 < ‖t‖) (ht1 : ‖t‖ < 1) :
    SphericallyCompleteSpace (closure (Subfield.closure {t} : Set K')) := by
  exact AlternatingAnalytic.sphericallyCompleteSpace_closure_subfieldClosure p t ht0 ht1

end AlternatingAnalyticChallenge.LemD_2
