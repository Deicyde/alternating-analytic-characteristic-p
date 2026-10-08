/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
import AlternatingAnalytic.Tensor.L1Projection.Basic
import AlternatingAnalytic.Analysis.DependentCZero
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# The tensor test family in independent universes

The necessity half of the analytic tensor criterion (`fam:thm:tensor-analytic`) with the scalar
field and the parameter space in independent universes. The dependent `c₀` sum of the tensor
powers `T_{m+1}(P)` lies in `Type (max uK uP)`, the pure-power map `x ↦ (x^{⊗ (m+1)})_m` is
analytic on the open unit ball, and universal analytic reflection therefore produces
projections `T_{m+1}(P) → Δ_{m+1}(P)` with norms bounded by `C r^(m+1)`. This follows
`AlternatingAnalytic.Analysis.TensorTestFamily` and `UniversalAnalyticReflection`, which fix a
single universe.
-/

noncomputable section

open Filter
open scoped Topology BigOperators ENNReal NNReal

namespace AlternatingAnalytic.L1Projection

universe uK uP

variable {K : Type uK} {P : Type uP} [NontriviallyNormedField K]
  [NormedAddCommGroup P] [NormedSpace K P]

/-- The dependent c₀ sum of the positive-degree completed tensor powers. -/
abbrev tensorTestSpace (K : Type uK) (P : Type uP) [NontriviallyNormedField K]
    [NormedAddCommGroup P] [NormedSpace K P] :=
  DependentCZero K (fun m : ℕ => TensorPower K P (m + 1))

/-- The coordinatewise closed diagonal submodule of the test space. -/
def tensorTestSubmodule : Submodule K (tensorTestSpace K P) :=
  DependentCZero.coordinateSubmodule (fun m => DiagonalSpan K P (m + 1))

instance : NormedAddCommGroup (tensorTestSubmodule (K := K) (P := P)) :=
  inferInstanceAs (NormedAddCommGroup
    (DependentCZero.coordinateSubmodule (fun m => DiagonalSpan K P (m + 1))))

instance : NormedSpace K (tensorTestSubmodule (K := K) (P := P)) :=
  inferInstanceAs (NormedSpace K
    (DependentCZero.coordinateSubmodule (fun m => DiagonalSpan K P (m + 1))))

theorem isClosed_tensorTestSubmodule :
    IsClosed (tensorTestSubmodule (K := K) (P := P) : Set (tensorTestSpace K P)) :=
  DependentCZero.isClosed_coordinateSubmodule _ (fun m => isClosed_diagonalSpan (m + 1))

/-- Ambient tensor coordinate, indexed from zero. -/
def tensorTestCoordinate (m : ℕ) : tensorTestSpace K P →L[K] TensorPower K P (m + 1) :=
  DependentCZero.eval m

/-- The diagonal-span-valued coordinate projection on the closed test submodule. -/
def tensorTestDeltaCoordinate (m : ℕ) :
    tensorTestSubmodule (K := K) (P := P) →L[K] DiagonalSpan K P (m + 1) :=
  DependentCZero.coordinateEval _ m

@[simp]
theorem tensorTestDeltaCoordinate_coe (m : ℕ)
    (z : tensorTestSubmodule (K := K) (P := P)) :
    (tensorTestDeltaCoordinate m z : TensorPower K P (m + 1)) =
      tensorTestCoordinate m (z : tensorTestSpace K P) := rfl

theorem norm_tensorTestDeltaCoordinate_le (m : ℕ) :
    ‖tensorTestDeltaCoordinate (K := K) (P := P) m‖ ≤ 1 :=
  DependentCZero.norm_coordinateEval_le _ m

/-- Pure powers on the unit ball, extended by zero elsewhere. -/
def tensorTestMap (x : P) : tensorTestSubmodule (K := K) (P := P) := by
  classical
  exact if hx : ‖x‖ < 1 then
    ⟨DependentCZero.ofGeometric (fun m => diagonalTensor K (m + 1) x)
      (C := 1) zero_le_one (norm_nonneg x) hx
      (fun m => by simpa using norm_diagonalTensor_le (K := K) (m + 1) x),
      (DependentCZero.mem_coordinateSubmodule _ _).2 (fun m => diagonalTensor_mem _ x)⟩
    else 0

theorem tensorTestMap_coordinate (x : P) (hx : ‖x‖ < 1) (m : ℕ) :
    tensorTestCoordinate m (tensorTestMap (K := K) x : tensorTestSpace K P) =
      diagonalTensor K (m + 1) x := by
  simp [tensorTestMap, hx, tensorTestCoordinate, DependentCZero.eval_apply]

/-- The ambient series: no constant term, and the canonical tensor map in coordinate `m` at
degree `m + 1`. -/
def tensorTestSeries : FormalMultilinearSeries K P (tensorTestSpace K P)
  | 0 => 0
  | m + 1 => (DependentCZero.single m).compContinuousMultilinearMap
      (completedProjectiveTensorTprod (fun _ : Fin (m + 1) => P))

theorem tensorTestSeries_zero : tensorTestSeries (K := K) (P := P) 0 = 0 := rfl

theorem tensorTestSeries_coordinate (m : ℕ) (v : Fin (m + 1) → P) :
    tensorTestCoordinate m (tensorTestSeries (K := K) (m + 1) v) =
      completedProjectiveTensorTprod (K := K) (fun _ : Fin (m + 1) => P) v :=
  DependentCZero.single_apply_self (K := K) _ _

theorem norm_tensorTestSeries_le (n : ℕ) :
    ‖tensorTestSeries (K := K) (P := P) n‖ ≤ 1 := by
  cases n with
  | zero => simp only [tensorTestSeries_zero, ContinuousMultilinearMap.opNorm_zero, zero_le_one]
  | succ m =>
    calc
      ‖tensorTestSeries (K := K) (P := P) (m + 1)‖ ≤
          ‖DependentCZero.single (K := K) (E := fun m => TensorPower K P (m + 1)) m‖ *
            ‖completedProjectiveTensorTprod (K := K) (fun _ : Fin (m + 1) => P)‖ :=
        ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
      _ ≤ 1 * 1 := mul_le_mul (DependentCZero.norm_single_le m)
        (norm_completedProjectiveTensorTprod_le _) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul _

theorem one_le_tensorTestSeries_radius :
    1 ≤ (tensorTestSeries (K := K) (P := P)).radius := by
  exact (tensorTestSeries (K := K) (P := P)).le_radius_of_bound (r := 1) 1
    (fun n => by simpa using norm_tensorTestSeries_le (K := K) (P := P) n)

theorem tensorTestSeries_hasSum (x : P) (hx : ‖x‖ < 1) :
    HasSum (fun n => tensorTestSeries (K := K) n (fun _ => x))
      (tensorTestMap (K := K) x : tensorTestSpace K P) := by
  let v : tensorTestSpace K P := (tensorTestMap (K := K) x).val
  have h : HasSum (fun m => DependentCZero.single (K := K) m (v m)) v := by
    simpa only [HasSum, SummationFilter.unconditional_filter,
      DependentCZero.truncate_eq_finiteVector, DependentCZero.finiteVector]
      using DependentCZero.tendsto_truncate v
  have he : (fun m => tensorTestSeries (K := K) (m + 1) (fun _ => x)) =
      (fun m => DependentCZero.single (K := K) m (v m)) := by
    funext m
    have hv : v m = diagonalTensor K (m + 1) x :=
      tensorTestMap_coordinate x hx m
    rw [hv]
    rfl
  have h' : HasSum (fun m => tensorTestSeries (K := K) (m + 1) (fun _ => x))
      (v - ∑ i ∈ Finset.range 1, tensorTestSeries (K := K) i (fun _ => x)) := by
    rw [he]
    simpa only [Finset.sum_range_one, tensorTestSeries_zero,
      zero_apply, sub_zero] using h
  exact (hasSum_nat_add_iff' 1).mp h'

theorem tensorTestMap_hasFPowerSeriesOnBall :
    HasFPowerSeriesOnBall
      (fun x : P => (tensorTestMap (K := K) x : tensorTestSpace K P)) tensorTestSeries 0 1 := by
  refine ⟨one_le_tensorTestSeries_radius, zero_lt_one, ?_⟩
  intro x hx
  have hball : Metric.eball (0 : P) (1 : ℝ≥0∞) = Metric.ball 0 1 := by
    simpa using (Metric.eball_coe (x := (0 : P)) (ε := (1 : ℝ≥0)))
  have hnorm : ‖x‖ < 1 := by simpa [hball, Metric.mem_ball, dist_zero_right] using hx
  simpa only [zero_add] using tensorTestSeries_hasSum (K := K) x hnorm

/-- The ambient test map is analytic on the open unit ball. -/
theorem tensorTestMap_analyticOnNhd :
    AnalyticOnNhd K (fun x : P => (tensorTestMap (K := K) x : tensorTestSpace K P))
      (Metric.ball 0 1) := by
  have hball : Metric.eball (0 : P) (1 : ℝ≥0∞) = Metric.ball 0 1 := by
    simpa using (Metric.eball_coe (x := (0 : P)) (ε := (1 : ℝ≥0)))
  rw [← hball]
  exact tensorTestMap_hasFPowerSeriesOnBall.analyticOnNhd

/-- A reflected expansion of the test map has the pure powers as its coordinate diagonals. -/
theorem tensorTest_expansion_deltaCoordinate
    {q : FormalMultilinearSeries K P (tensorTestSubmodule (K := K) (P := P))}
    (hq : HasFPowerSeriesAt (tensorTestMap (K := K) (P := P)) q 0)
    (m : ℕ) (x : P) :
    (tensorTestDeltaCoordinate m (q (m + 1) (fun _ => x)) : TensorPower K P (m + 1)) =
      diagonalTensor K (m + 1) x := by
  let j := (tensorTestSubmodule (K := K) (P := P)).subtypeL
  have hjq : HasFPowerSeriesAt
      (fun x : P => (tensorTestMap (K := K) x : tensorTestSpace K P))
      (j.compFormalMultilinearSeries q) 0 := by
    obtain ⟨r, hr⟩ := hq
    exact ⟨r, j.comp_hasFPowerSeriesOnBall hr⟩
  have ha : HasFPowerSeriesAt
      (fun x : P => (tensorTestMap (K := K) x : tensorTestSpace K P))
      tensorTestSeries 0 := ⟨1, tensorTestMap_hasFPowerSeriesOnBall⟩
  have hz : HasFPowerSeriesAt (0 : P → tensorTestSpace K P)
      (j.compFormalMultilinearSeries q - tensorTestSeries) 0 := by
    simpa only [sub_self] using hjq.sub ha
  have hd := hz.apply_eq_zero (m + 1) x
  have he : j (q (m + 1) (fun _ => x)) =
      tensorTestSeries (K := K) (m + 1) (fun _ => x) := by
    exact sub_eq_zero.mp hd
  simpa only [tensorTestDeltaCoordinate_coe, j, Submodule.subtypeL_apply,
    tensorTestSeries_coordinate, diagonalTensor_eq] using
      congrArg (tensorTestCoordinate m) he

/-- The linearization of the selected coordinate of one reflected series coefficient. -/
def tensorTestProjection
    (q : FormalMultilinearSeries K P (tensorTestSubmodule (K := K) (P := P))) (m : ℕ) :
    TensorPower K P (m + 1) →L[K] DiagonalSpan K P (m + 1) :=
  completedProjectiveTensorLiftIsometry (fun _ : Fin (m + 1) => P)
    (DiagonalSpan K P (m + 1))
    ((tensorTestDeltaCoordinate m).compContinuousMultilinearMap (q (m + 1)))

theorem tensorTestProjection_fixes
    {q : FormalMultilinearSeries K P (tensorTestSubmodule (K := K) (P := P))}
    (hq : HasFPowerSeriesAt (tensorTestMap (K := K) (P := P)) q 0) (m : ℕ)
    (t : DiagonalSpan K P (m + 1)) :
    tensorTestProjection q m (t : TensorPower K P (m + 1)) = t := by
  apply fixes_of_fixes_diagonalTensor
  intro x
  rw [diagonalTensor_eq, tensorTestProjection, completedProjectiveTensorLiftIsometry_tprod,
    ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply]
  exact tensorTest_expansion_deltaCoordinate hq m x

theorem norm_tensorTestProjection_le
    (q : FormalMultilinearSeries K P (tensorTestSubmodule (K := K) (P := P))) (m : ℕ) :
    ‖tensorTestProjection q m‖ ≤ ‖q (m + 1)‖ := by
  calc
    ‖tensorTestProjection q m‖ =
        ‖(tensorTestDeltaCoordinate m).compContinuousMultilinearMap (q (m + 1))‖ :=
      norm_completedProjectiveTensorLiftIsometry _ _
    _ ≤ ‖tensorTestDeltaCoordinate (K := K) (P := P) m‖ * ‖q (m + 1)‖ :=
      ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ ≤ 1 * ‖q (m + 1)‖ := mul_le_mul_of_nonneg_right
      (norm_tensorTestDeltaCoordinate_le m) (norm_nonneg _)
    _ = ‖q (m + 1)‖ := one_mul _

/-- Universal analytic reflection gives projections onto the diagonal spans with a common
exponential norm bound (the necessity half of `fam:thm:tensor-analytic`). -/
theorem tensor_projections_of_universalAnalyticReflection
    (h : UniversalAnalyticReflection K P) :
    ∃ R : ∀ m : ℕ, TensorPower K P (m + 1) →L[K] DiagonalSpan K P (m + 1),
      (∀ (m : ℕ) (t : DiagonalSpan K P (m + 1)), R m (t : TensorPower K P (m + 1)) = t) ∧
      ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ ∀ m, ‖R m‖ ≤ C * r ^ (m + 1) := by
  have : CompleteSpace (tensorTestSubmodule (K := K) (P := P)) :=
    isClosed_tensorTestSubmodule.completeSpace_coe
  have ha : AnalyticAt K (tensorTestMap (K := K) (P := P)) 0 :=
    h (tensorTestSpace K P) tensorTestSubmodule isClosed_tensorTestSubmodule
      (Metric.ball 0 1) Metric.isOpen_ball tensorTestMap tensorTestMap_analyticOnNhd
      0 (by simp)
  obtain ⟨q, hq⟩ := ha
  obtain ⟨C, r, hC, hr, hbound⟩ := q.le_mul_pow_of_radius_pos hq.radius_pos
  exact ⟨tensorTestProjection q, tensorTestProjection_fixes hq, C, r, hC, hr,
    fun m => (norm_tensorTestProjection_le q m).trans (hbound (m + 1))⟩

end AlternatingAnalytic.L1Projection
