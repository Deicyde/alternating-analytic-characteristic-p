import AlternatingAnalytic.Analysis.HomogeneousTensorReflection
import AlternatingAnalytic.Analysis.DependentCZero
import Mathlib.Analysis.Analytic.ChangeOrigin

/-!
# The analytic dependent c₀ tensor test family

The necessity test family from `fam:thm:tensor-analytic`. Coordinate `m` has tensor
degree `m + 1`. The pure-power family is defined on the open unit ball and extended
by zero outside it. Its ambient expansion has zero constant coefficient, and Mathlib's
change-of-origin theorem gives analyticity throughout the whole open ball.
-/

noncomputable section

open Filter
open scoped Topology BigOperators ENNReal NNReal

namespace AlternatingAnalytic

universe u

variable {K P : Type u} [NontriviallyNormedField K]
  [NormedAddCommGroup P] [NormedSpace K P]

/-- The dependent c₀ sum of the positive-degree completed tensor powers. -/
abbrev tensorTestSpace (K P : Type u) [NontriviallyNormedField K]
    [NormedAddCommGroup P] [NormedSpace K P] :=
  DependentCZero K (fun m : ℕ => TensorPower K P (m + 1))

/-- The actual coordinatewise closed diagonal submodule of the test space. -/
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

instance : CompleteSpace (tensorTestSubmodule (K := K) (P := P)) :=
  isClosed_tensorTestSubmodule.completeSpace_coe

/-- Identification with the dependent c₀ sum of the diagonal spans, preserving norms. -/
def tensorTestCoordinateEquiv :
    DependentCZero K (fun m : ℕ => DiagonalSpan K P (m + 1)) ≃ₗᵢ[K]
      tensorTestSubmodule (K := K) (P := P) :=
  DependentCZero.coordinateEquiv _

/-- Ambient tensor coordinate, indexed from zero. -/
def tensorTestCoordinate (m : ℕ) : tensorTestSpace K P →L[K] TensorPower K P (m + 1) :=
  DependentCZero.eval m

theorem norm_tensorTestCoordinate_le (m : ℕ) :
    ‖tensorTestCoordinate (K := K) (P := P) m‖ ≤ 1 :=
  DependentCZero.norm_eval_le m

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

theorem norm_diagonalTensor_le (n : ℕ) (x : P) :
    ‖diagonalTensor (K := K) n x‖ ≤ ‖x‖ ^ n := by
  calc
    ‖diagonalTensor (K := K) n x‖ ≤
        ‖completedProjectiveTensorTprod (K := K) (fun _ : Fin n => P)‖ * ‖x‖ ^ n := by
      simpa [diagonalTensor] using
        (completedProjectiveTensorTprod (K := K) (fun _ : Fin n => P)).le_opNorm
          (fun _ => x)
    _ ≤ 1 * ‖x‖ ^ n := mul_le_mul_of_nonneg_right
      (norm_completedProjectiveTensorTprod_le _) (pow_nonneg (norm_nonneg x) _)
    _ = ‖x‖ ^ n := one_mul _

/-- Pure powers on the unit ball, extended by zero elsewhere. -/
def tensorTestMap (x : P) : tensorTestSubmodule (K := K) (P := P) := by
  classical
  exact if hx : ‖x‖ < 1 then
    ⟨DependentCZero.ofGeometric (fun m => diagonalTensor (K := K) (m + 1) x)
      (C := 1) zero_le_one (norm_nonneg x) hx
      (fun m => by simpa using norm_diagonalTensor_le (K := K) (m + 1) x),
      (DependentCZero.mem_coordinateSubmodule _ _).2 (fun m => diagonalTensor_mem _ x)⟩
    else 0

@[simp]
theorem tensorTestMap_coordinate (x : P) (hx : ‖x‖ < 1) (m : ℕ) :
    tensorTestCoordinate m (tensorTestMap (K := K) x : tensorTestSpace K P) =
      diagonalTensor (K := K) (m + 1) x := by
  simp [tensorTestMap, hx, tensorTestCoordinate, DependentCZero.eval_apply]

theorem tensorTestMap_eq_zero (x : P) (hx : ¬ ‖x‖ < 1) :
    tensorTestMap (K := K) x = 0 := by
  simp [tensorTestMap, hx]

theorem tensorTestMap_deltaCoordinate (x : P) (hx : ‖x‖ < 1) (m : ℕ) :
    tensorTestDeltaCoordinate m (tensorTestMap (K := K) x) =
      ⟨diagonalTensor (K := K) (m + 1) x, diagonalTensor_mem _ x⟩ := by
  apply Subtype.ext
  exact tensorTestMap_coordinate x hx m

/-- The explicit ambient series: no constant term, and the canonical tensor map in
coordinate `m` at degree `m + 1`. -/
def tensorTestSeries : FormalMultilinearSeries K P (tensorTestSpace K P)
  | 0 => 0
  | m + 1 => (DependentCZero.single m).compContinuousMultilinearMap
      (completedProjectiveTensorTprod (fun _ : Fin (m + 1) => P))

@[simp]
theorem tensorTestSeries_zero : tensorTestSeries (K := K) (P := P) 0 = 0 := rfl

@[simp]
theorem tensorTestSeries_succ (m : ℕ) :
    tensorTestSeries (K := K) (P := P) (m + 1) =
      (DependentCZero.single m).compContinuousMultilinearMap
        (completedProjectiveTensorTprod (fun _ : Fin (m + 1) => P)) := rfl

@[simp]
theorem tensorTestSeries_coordinate (m : ℕ) (v : Fin (m + 1) → P) :
    tensorTestCoordinate m (tensorTestSeries (K := K) (m + 1) v) =
      completedProjectiveTensorTprod (K := K) (fun _ : Fin (m + 1) => P) v :=
  DependentCZero.single_apply_self (K := K) _ _

theorem tensorTestSeries_coordinate_ne (m n : ℕ) (h : n ≠ m + 1) (v : Fin n → P) :
    tensorTestCoordinate m (tensorTestSeries (K := K) n v) = 0 := by
  cases n with
  | zero => simp [tensorTestSeries]
  | succ n =>
    exact DependentCZero.single_apply_ne (K := K) n _ (fun hmn => h (by omega))

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

/-- The coefficient diagonals sum to the concrete pure-power vector, by convergence
of dependent c₀ truncations. The index shift accounts for the zero constant term. -/
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
    have hv : v m = diagonalTensor (K := K) (m + 1) x :=
      tensorTestMap_coordinate x hx m
    rw [hv]
    rfl
  have h' : HasSum (fun m => tensorTestSeries (K := K) (m + 1) (fun _ => x))
      (v - ∑ i ∈ Finset.range 1, tensorTestSeries (K := K) i (fun _ => x)) := by
    rw [he]
    simpa only [Finset.sum_range_one, tensorTestSeries_zero,
      zero_apply, sub_zero] using h
  exact (hasSum_nat_add_iff' 1).mp h'

/-- The actual ambient expansion on the ball of radius one. -/
theorem tensorTestMap_hasFPowerSeriesOnBall :
    HasFPowerSeriesOnBall
      (fun x : P => (tensorTestMap (K := K) x : tensorTestSpace K P)) tensorTestSeries 0 1 := by
  refine ⟨one_le_tensorTestSeries_radius, zero_lt_one, ?_⟩
  intro x hx
  have hball : Metric.eball (0 : P) (1 : ℝ≥0∞) = Metric.ball 0 1 := by
    simpa using (Metric.eball_coe (x := (0 : P)) (ε := (1 : ℝ≥0)))
  have hnorm : ‖x‖ < 1 := by simpa [hball, Metric.mem_ball, dist_zero_right] using hx
  simpa only [zero_add] using tensorTestSeries_hasSum (K := K) x hnorm

/-- Ambient analyticity at every point of the open unit ball, supplied by Mathlib's
complete-output change-of-origin theorem. -/
theorem tensorTestMap_analyticOnNhd :
    AnalyticOnNhd K (fun x : P => (tensorTestMap (K := K) x : tensorTestSpace K P))
      (Metric.ball 0 1) := by
  have hball : Metric.eball (0 : P) (1 : ℝ≥0∞) = Metric.ball 0 1 := by
    simpa using (Metric.eball_coe (x := (0 : P)) (ε := (1 : ℝ≥0)))
  rw [← hball]
  exact tensorTestMap_hasFPowerSeriesOnBall.analyticOnNhd

/-- The complete test-family statement: the concrete diagonal subspace is closed,
the map has exact pure-power coordinates, its coefficients are contractions, and its
ambient expansion is analytic throughout the open unit ball. -/
theorem tensor_test_family [CompleteSpace K] [CompleteSpace P] :
    IsClosed (tensorTestSubmodule (K := K) (P := P) : Set (tensorTestSpace K P)) ∧
    (∀ x : P, ‖x‖ < 1 → ∀ m,
      tensorTestCoordinate m (tensorTestMap (K := K) x : tensorTestSpace K P) =
        diagonalTensor (K := K) (m + 1) x) ∧
    (∀ n, ‖tensorTestSeries (K := K) (P := P) n‖ ≤ 1) ∧
    HasFPowerSeriesOnBall
      (fun x : P => (tensorTestMap (K := K) x : tensorTestSpace K P)) tensorTestSeries 0 1 ∧
    AnalyticOnNhd K
      (fun x : P => (tensorTestMap (K := K) x : tensorTestSpace K P)) (Metric.ball 0 1) :=
  ⟨isClosed_tensorTestSubmodule, tensorTestMap_coordinate, norm_tensorTestSeries_le,
    tensorTestMap_hasFPowerSeriesOnBall, tensorTestMap_analyticOnNhd⟩

end AlternatingAnalytic
