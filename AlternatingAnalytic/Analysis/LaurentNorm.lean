import Mathlib.RingTheory.LaurentSeries
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Data.Int.WithZero
import AlternatingAnalytic.Analysis.SphericalCompleteness

/-!
# The norm `‖x‖ = r ^ order x` on Laurent series

For `0 < r < 1` we put on `LaurentSeries κ` the norm coming from its valuation with `‖X‖ = r`,
and show it is complete, ultrametric and spherically complete. The normed field structures are
definitions, not instances, so no radius is fixed globally; `LaurentField` installs them.
-/

noncomputable section

open scoped NNReal WithZero
open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀

namespace AlternatingAnalytic

variable (κ : Type*) [Field κ] {r : ℝ≥0}

/-- The rank-one structure on the Laurent valuation with `‖X‖ = r`. -/
@[instance_reducible]
def laurentRankOne (hr0 : 0 < r) (hr1 : r < 1) :
    (Valued.v (R := LaurentSeries κ)).RankOne where
  hom' := (WithZeroMulInt.toNNReal (inv_ne_zero hr0.ne')).comp embedding
  strictMono' := (WithZeroMulInt.toNNReal_strictMono
    ((one_lt_inv₀ hr0).2 hr1)).comp embedding_strictMono
  exists_val_nontrivial := by
    obtain ⟨x, hx⟩ := LaurentSeries.valuation_surjective κ (WithZero.exp (1 : ℤ))
    refine ⟨x, ?_, ?_⟩
    · intro h
      exact WithZero.exp_ne_zero (hx.symm.trans h)
    · rw [hx]
      simp

/-- The nontrivially normed field structure on Laurent series with `‖X‖ = r`. -/
@[instance_reducible]
def laurentNormedField (hr0 : 0 < r) (hr1 : r < 1) :
    NontriviallyNormedField (LaurentSeries κ) :=
  let := laurentRankOne κ hr0 hr1
  Valued.toNontriviallyNormedField (LaurentSeries κ) ℤᵐ⁰

/-- The valuation of a nonzero Laurent series is `exp (-order x)`. -/
theorem laurent_valuation_eq_order (x : LaurentSeries κ) (hx : x ≠ 0) :
    Valued.v x = WithZero.exp (-x.order) := by
  have hv0 : Valued.v x ≠ 0 := by simpa using hx
  have hupper : WithZero.log (Valued.v x) ≤ -x.order := by
    apply (WithZero.log_le_iff_le_exp hv0).2
    exact (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero κ).2
      (fun _ h => HahnSeries.coeff_eq_zero_of_lt_order h)
  have hlower : -x.order ≤ WithZero.log (Valued.v x) := by
    by_contra h
    have hvle : Valued.v x ≤ WithZero.exp (-(x.order + 1)) :=
      (WithZero.log_le_iff_le_exp hv0).1 (by omega)
    have hz := LaurentSeries.coeff_zero_of_lt_valuation κ hvle
      (show x.order < x.order + 1 by omega)
    exact hx (HahnSeries.coeff_order_eq_zero.mp hz)
  rw [← WithZero.exp_log hv0, le_antisymm hupper hlower]

variable (hr0 : 0 < r) (hr1 : r < 1)

theorem laurent_norm_eq (x : LaurentSeries κ) :
    let := laurentNormedField κ hr0 hr1
    ‖x‖ = (WithZeroMulInt.toNNReal (inv_ne_zero hr0.ne') (Valued.v x) : ℝ≥0) := by
  let := laurentNormedField κ hr0 hr1
  change ((WithZeroMulInt.toNNReal (inv_ne_zero hr0.ne'))
    (embedding (Valued.v.restrict x)) : ℝ) = _
  rw [Valuation.restrict_def, ValueGroup₀.embedding_restrict₀]
  rfl

theorem laurent_norm_single_one (n : ℤ) :
    let := laurentNormedField κ hr0 hr1
    ‖(HahnSeries.single n 1 : LaurentSeries κ)‖ = (r : ℝ) ^ n := by
  let := laurentNormedField κ hr0 hr1
  change ‖(HahnSeries.single n 1 : LaurentSeries κ)‖ = (r : ℝ) ^ n
  rw [laurent_norm_eq κ hr0 hr1, LaurentSeries.valuation_single_zpow]
  simp [WithZeroMulInt.toNNReal, WithZero.exp, zpow_neg]

include hr0 hr1 in
theorem laurent_completeSpace :
    let := laurentNormedField κ hr0 hr1
    CompleteSpace (LaurentSeries κ) := by
  let := laurentNormedField κ hr0 hr1
  infer_instance

theorem laurent_isUltrametricDist :
    let := laurentNormedField κ hr0 hr1
    IsUltrametricDist (LaurentSeries κ) := by
  let := laurentRankOne κ hr0 hr1
  let := laurentNormedField κ hr0 hr1
  infer_instance

/-- A nonzero Laurent series has norm `r ^ order x`. -/
theorem laurent_norm_of_ne_zero (x : LaurentSeries κ) (hx : x ≠ 0) :
    letI := laurentNormedField κ hr0 hr1
    ‖x‖ = (r : ℝ) ^ x.order := by
  let := laurentNormedField κ hr0 hr1
  change ‖x‖ = (r : ℝ) ^ x.order
  rw [laurent_norm_eq κ hr0 hr1, laurent_valuation_eq_order κ x hx]
  simp [WithZeroMulInt.toNNReal, WithZero.exp, zpow_neg]

/-- A nonzero monomial `c X^n` has norm `r ^ n`. -/
theorem laurent_norm_single (n : ℤ) (c : κ) (hc : c ≠ 0) :
    letI := laurentNormedField κ hr0 hr1
    ‖(HahnSeries.single n c : LaurentSeries κ)‖ = (r : ℝ) ^ n := by
  let := laurentNormedField κ hr0 hr1
  change ‖(HahnSeries.single n c : LaurentSeries κ)‖ = (r : ℝ) ^ n
  rw [laurent_norm_of_ne_zero κ hr0 hr1 _ (HahnSeries.single_ne_zero hc),
    HahnSeries.order_single hc]

/-- Nonzero constant Laurent series have norm one. -/
theorem laurent_norm_algebraMap (c : κ) (hc : c ≠ 0) :
    letI := laurentNormedField κ hr0 hr1
    ‖algebraMap κ (LaurentSeries κ) c‖ = 1 := by
  let := laurentNormedField κ hr0 hr1
  simpa only [LaurentSeries.algebraMap_apply, HahnSeries.C_apply, zpow_zero] using laurent_norm_single κ hr0 hr1 0 c hc

/-- The norm takes values in `r^ℤ ∪ {0}`, so the field is spherically complete. -/
theorem laurent_sphericallyCompleteSpace :
    letI := laurentNormedField κ hr0 hr1
    SphericallyCompleteSpace (LaurentSeries κ) := by
  let := laurentRankOne κ hr0 hr1
  let := laurentNormedField κ hr0 hr1
  have h0 : 0 < (r : ℝ) := hr0
  have h1 : (r : ℝ) < 1 := hr1
  apply sphericallyCompleteSpace_of_discreteNorm ((one_lt_inv₀ h0).2 h1)
  intro x hx
  refine ⟨-x.order, ?_⟩
  rw [laurent_norm_of_ne_zero κ hr0 hr1 x hx]
  simp [zpow_neg]

/-- A Laurent series of norm less than one has zero constant coefficient. -/
theorem laurent_coeff_zero_of_norm_lt_one (x : LaurentSeries κ) :
    letI := laurentNormedField κ hr0 hr1
    ‖x‖ < 1 → x.coeff 0 = 0 := by
  let := laurentNormedField κ hr0 hr1
  intro h
  by_cases hx : x = 0
  · simp [hx]
  · rw [laurent_norm_of_ne_zero κ hr0 hr1 x hx] at h
    exact HahnSeries.coeff_eq_zero_of_lt_order
      ((zpow_lt_one_iff_right_of_lt_one₀ (show 0 < (r : ℝ) from hr0)
        (show (r : ℝ) < 1 from hr1)).1 h)

end AlternatingAnalytic
