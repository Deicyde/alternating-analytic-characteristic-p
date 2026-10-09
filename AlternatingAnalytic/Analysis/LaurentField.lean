import AlternatingAnalytic.Analysis.LaurentNorm
import Mathlib.Algebra.CharP.Algebra

/-!
# The Laurent series field `κ((X))` with `‖X‖ = r`

`LaurentField κ r` is `LaurentSeries κ` with the norm `‖x‖ = r ^ order x` for `0 < r < 1`.
It is a complete, ultrametric, spherically complete nontrivially normed field. This is the
field `K₁ = κ((X))` of Appendix C.
-/

noncomputable section

open scoped NNReal

namespace AlternatingAnalytic

/-- Laurent series over `κ`. The radius `r` is a type parameter so that the norm is an instance. -/
def LaurentField (κ : Type*) [Field κ] (_r : ℝ≥0) := LaurentSeries κ

namespace LaurentField

variable (κ : Type*) [Field κ] (r : ℝ≥0)

instance : Field (LaurentField κ r) := inferInstanceAs (Field (LaurentSeries κ))

instance : Algebra κ (LaurentField κ r) := inferInstanceAs (Algebra κ (LaurentSeries κ))

instance (p : ℕ) [CharP κ p] : CharP (LaurentField κ r) p :=
  charP_of_injective_algebraMap (algebraMap κ (LaurentField κ r)).injective p

/-- The `X^n`-coefficient, as a `κ`-linear map. -/
noncomputable def coeff (n : ℤ) : LaurentField κ r →ₗ[κ] κ where
  toFun x := (show LaurentSeries κ from x).coeff n
  map_add' x y := HahnSeries.coeff_add
  map_smul' c x := by
    rw [Algebra.smul_def]
    change ((algebraMap κ (LaurentSeries κ) c) * (show LaurentSeries κ from x)).coeff n =
      c * (show LaurentSeries κ from x).coeff n
    rw [LaurentSeries.algebraMap_apply, HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]

@[simp]
theorem coeff_apply (n : ℤ) (x : LaurentField κ r) :
    coeff κ r n x = (show LaurentSeries κ from x).coeff n := rfl

variable [Fact (0 < r)] [Fact (r < 1)]

noncomputable instance : NontriviallyNormedField (LaurentField κ r) :=
  laurentNormedField κ (r := r) Fact.out Fact.out

instance : CompleteSpace (LaurentField κ r) :=
  laurent_completeSpace κ (show 0 < r from Fact.out) (show r < 1 from Fact.out)

instance : IsUltrametricDist (LaurentField κ r) :=
  laurent_isUltrametricDist κ (show 0 < r from Fact.out) (show r < 1 from Fact.out)

instance : SphericallyCompleteSpace (LaurentField κ r) :=
  laurent_sphericallyCompleteSpace κ (show 0 < r from Fact.out) (show r < 1 from Fact.out)

theorem norm_of_ne_zero (x : LaurentField κ r) (hx : x ≠ 0) :
    ‖x‖ = (r : ℝ) ^ (show LaurentSeries κ from x).order :=
  laurent_norm_of_ne_zero κ (r := r) Fact.out Fact.out x hx

theorem norm_algebraMap (c : κ) (hc : c ≠ 0) :
    ‖algebraMap κ (LaurentField κ r) c‖ = 1 :=
  laurent_norm_algebraMap κ (r := r) Fact.out Fact.out c hc

theorem norm_algebraMap_le_one (c : κ) : ‖algebraMap κ (LaurentField κ r) c‖ ≤ 1 := by
  by_cases hc : c = 0
  · subst c
    have hz : ‖(0 : LaurentField κ r)‖ = 0 := norm_zero
    simpa only [map_zero] using hz.le.trans zero_le_one
  · exact (norm_algebraMap κ r c hc).le

theorem coeff_zero_of_norm_lt_one (x : LaurentField κ r) (hx : ‖x‖ < 1) :
    coeff κ r 0 x = 0 :=
  laurent_coeff_zero_of_norm_lt_one κ (r := r) Fact.out Fact.out x hx

end LaurentField

end AlternatingAnalytic
