import AlternatingAnalytic.Analysis.LaurentField
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Algebra.Field.ZMod

/-!
# Lemma D.2 (Laurent subfield), p. 42

Paper statement: "Let K′ be a complete nontrivially normed field of characteristic p, and let
t ∈ K′ with 0 < |t| = r < 1.
(1) K′ is nonarchimedean, and |c| = 1 for every c ∈ 𝔽_p^×.
(2) For a_m, …, a_M ∈ 𝔽_p, not all zero, |∑_{i=m}^{M} a_i t^i| = r^{min{i : a_i ≠ 0}}.
(3) Give 𝔽_p((X)) the absolute value with |X| = r. There is a continuous isometric ring
homomorphism ev_t : 𝔽_p((X)) → K′ such that ev_t(∑_{i≥m} a_i X^i) = ∑_{i≥m} a_i t^i. Its
image K₁ is a closed subfield of K′; it is the closure of 𝔽_p(t), and it is isometrically
isomorphic to 𝔽_p((X)).
(4) K₁ is spherically complete."

## Formalization notes

* `𝔽_p` is `ZMod p` for a prime `p` with `[CharP K′ p]`, mapped into `K′` by
  `ZMod.castHom (dvd_refl p) K′`.
* (1): "nonarchimedean" is `IsUltrametricDist K′`.
* (2): the coefficients are `a : ℤ → ZMod p` on `Finset.Icc m M`. The minimum
  `min{i : a_i ≠ 0}` is an index `i₀` in the window with `a i₀ ≠ 0` and `i₀ ≤ i` whenever
  `a i ≠ 0`.
* (3), (4): `r : ℝ≥0` with `[Fact (0 < r)]`, `[Fact (r < 1)]` and `‖t‖ = r`. `𝔽_p((X))` with
  `|X| = r` is `AlternatingAnalytic.LaurentField (ZMod p) r`, a type synonym of
  `LaurentSeries (ZMod p)` with `‖x‖ = r ^ (order x)` and coefficients
  `LaurentField.coeff (ZMod p) r i`.
* (3): the evaluation formula is a `HasSum` over `ℤ`. "The closure of 𝔽_p(t)" is the closure of
  `Subfield.closure {t}`. "Isometrically isomorphic to 𝔽_p((X))" is not stated separately; it
  follows from `Isometry ev`.
* (4) is stated for `K₁ = closure (Subfield.closure {t})` as a subtype of `K′`.
  `SphericallyCompleteSpace` is the library class from
  `AlternatingAnalytic/Analysis/SphericalCompleteness.lean`.
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
  sorry

/-- A sum `∑_{i=m}^{M} a_i t^i` with not all `a_i` zero has norm `‖t‖ ^ i₀`, where `i₀` is
the least index with `a_{i₀} ≠ 0`. -/
theorem part2
    (K' : Type u) [NontriviallyNormedField K'] [CompleteSpace K']
    (p : ℕ) [Fact p.Prime] [CharP K' p]
    (t : K') (ht0 : 0 < ‖t‖) (ht1 : ‖t‖ < 1)
    (m M : ℤ) (a : ℤ → ZMod p) (i₀ : ℤ) (hi₀ : i₀ ∈ Finset.Icc m M) (ha : a i₀ ≠ 0)
    (hmin : ∀ i ∈ Finset.Icc m M, a i ≠ 0 → i₀ ≤ i) :
    ‖∑ i ∈ Finset.Icc m M, ZMod.castHom (dvd_refl p) K' (a i) * t ^ i‖ = ‖t‖ ^ i₀ := by
  sorry

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
  sorry

/-- The closure of `𝔽_p(t)` in `K′` is spherically complete. -/
theorem part4
    (K' : Type u) [NontriviallyNormedField K'] [CompleteSpace K']
    (p : ℕ) [Fact p.Prime] [CharP K' p]
    (t : K') (ht0 : 0 < ‖t‖) (ht1 : ‖t‖ < 1) :
    SphericallyCompleteSpace (closure (Subfield.closure {t} : Set K')) := by
  sorry

end AlternatingAnalyticChallenge.LemD_2
