import AlternatingAnalytic.Analysis.PolynomialEvaluationNorm
import AlternatingAnalytic.Analysis.LaurentField
import Mathlib.Topology.Algebra.UniformRing

/-!
# Evaluation of polynomials at an element of norm `r`

For finite `κ` and `t` in a nonarchimedean field with `‖t‖ = r`, evaluating a polynomial
over `κ` at `t` preserves its norm in `κ((X))`. This is the isometry part of Lemma D.2.
-/

noncomputable section

open scoped NNReal RatFunc

namespace AlternatingAnalytic

variable (κ : Type*) [Field κ] (r : ℝ≥0)

/-- The inclusion of `κ[X]` into `κ((X))` with absolute value radius `r`. -/
def polynomialToLaurentField : Polynomial κ →+* LaurentField κ r :=
  algebraMap (Polynomial κ) (LaurentSeries κ)

@[simp]
theorem polynomialToLaurentField_C (c : κ) :
    polynomialToLaurentField κ r (Polynomial.C c) = algebraMap κ (LaurentField κ r) c := by
  change algebraMap (Polynomial κ) (LaurentSeries κ) (algebraMap κ (Polynomial κ) c) =
    algebraMap κ (LaurentSeries κ) c
  rw [Polynomial.algebraMap_hahnSeries_apply, LaurentSeries.algebraMap_apply]
  simp

@[simp]
theorem polynomialToLaurentField_X :
    polynomialToLaurentField κ r Polynomial.X = HahnSeries.single 1 1 := by
  change algebraMap (Polynomial κ) (LaurentSeries κ) Polynomial.X = HahnSeries.single 1 1
  simp [Polynomial.algebraMap_hahnSeries_apply]

theorem polynomialToLaurentField_eq_eval₂ :
    polynomialToLaurentField κ r = Polynomial.eval₂RingHom
      (algebraMap κ (LaurentField κ r)) (polynomialToLaurentField κ r Polynomial.X) := by
  apply Polynomial.ringHom_ext
  · intro c
    change polynomialToLaurentField κ r (Polynomial.C c) =
      Polynomial.eval₂ (algebraMap κ (LaurentField κ r))
        (polynomialToLaurentField κ r Polynomial.X) (Polynomial.C c)
    rw [Polynomial.eval₂_C, polynomialToLaurentField_C]
  · change polynomialToLaurentField κ r Polynomial.X =
      Polynomial.eval₂ (algebraMap κ (LaurentField κ r))
        (polynomialToLaurentField κ r Polynomial.X) Polynomial.X
    rw [Polynomial.eval₂_X]

/-- The inclusion of `κ(X)` into `κ((X))`. -/
def ratFuncToLaurentField : RatFunc κ →+* LaurentField κ r :=
  algebraMap (RatFunc κ) (LaurentSeries κ)

@[simp]
theorem ratFuncToLaurentField_polynomial (p : Polynomial κ) :
    ratFuncToLaurentField κ r (algebraMap (Polynomial κ) (RatFunc κ) p) =
      polynomialToLaurentField κ r p := by
  exact (IsScalarTower.algebraMap_apply (Polynomial κ) (RatFunc κ) (LaurentSeries κ) p).symm

variable [Fact (0 < r)] [Fact (r < 1)]

theorem norm_polynomialToLaurentField_X :
    ‖polynomialToLaurentField κ r Polynomial.X‖ = r := by
  rw [polynomialToLaurentField_X]
  exact (laurent_norm_single_one κ (r := r) Fact.out Fact.out 1).trans (zpow_one _)

variable [Finite κ] {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- Evaluation at `t` with `‖t‖ = r` has the same norm as the Laurent series. -/
theorem norm_polynomial_eval₂_eq_laurent (f : κ →+* K) (t : K) (ht : ‖t‖ = r)
    (p : Polynomial κ) :
    ‖p.eval₂ f t‖ = ‖polynomialToLaurentField κ r p‖ := by
  by_cases hp : p = 0
  · subst p
    have hz : ‖(0 : LaurentField κ r)‖ = 0 := norm_zero
    simpa only [Polynomial.eval₂_zero, norm_zero, map_zero] using hz.symm
  have hr0 : (0 : ℝ) < r := NNReal.coe_pos.mpr Fact.out
  have hr1 : (r : ℝ) < 1 := NNReal.coe_lt_one.mpr Fact.out
  have ht0 : t ≠ 0 := norm_pos_iff.mp (ht.symm ▸ hr0)
  have hX := norm_polynomialToLaurentField_X κ r
  have hX0 : polynomialToLaurentField κ r Polynomial.X ≠ 0 :=
    norm_pos_iff.mp (hX.symm ▸ hr0)
  rw [norm_polynomial_eval₂ f t ht0 (ht.symm ▸ hr1) p hp,
    polynomialToLaurentField_eq_eval₂ κ r]
  change ‖t‖ ^ p.natTrailingDegree =
    ‖p.eval₂ (algebraMap κ (LaurentField κ r))
      (polynomialToLaurentField κ r Polynomial.X)‖
  have hnorm := norm_polynomial_eval₂
    (K := LaurentField κ r) (algebraMap κ (LaurentField κ r))
    (polynomialToLaurentField κ r Polynomial.X) hX0 (hX.symm ▸ hr1) p hp
  exact (congrArg (fun a : ℝ => a ^ p.natTrailingDegree) (ht.trans hX.symm)).trans hnorm.symm

end AlternatingAnalytic
