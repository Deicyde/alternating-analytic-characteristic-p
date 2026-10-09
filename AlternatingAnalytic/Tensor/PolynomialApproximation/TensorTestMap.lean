/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
import AlternatingAnalytic.Tensor.PolynomialApproximation.SmoothReflection
import AlternatingAnalytic.Analysis.UniversalAnalyticReflection
import AlternatingAnalytic.Analysis.L1PolynomialLift
import Mathlib.Topology.Algebra.Order.Floor

/-!
# The tensor test map for Corollary G.5

The tensor test map `x ↦ (x^{⊗ (m+1)})ₘ` of `TensorTestFamily` is analytic into the dependent
`c₀` sum `Z` of tensor powers, and `C^∞` on the open unit ball as a map into the closed
diagonal subspace `W`, by smooth reflection through the closed isometric inclusion. When `P` is
ordinary `ℓ¹(ℕ,K)`, each ambient coefficient has a `W`-valued representative with the same
diagonal (`L1PolynomialLift.exists_l1_diagonal_lift`), so the truncations of the expansion are
entire `W`-valued polynomials converging uniformly on every smaller closed ball. If every
projection `T_n(P) → Δ_n(P)` has norm at least `n!` (Proposition G.4), the linearized
coefficients of a `W`-valued expansion at zero would be projections with exponentially bounded
norms, so the map is not analytic into `W` at zero.
-/

noncomputable section

open Filter
open scoped Topology NNReal ENNReal ContDiff

namespace AlternatingAnalytic.PolynomialApproximation

universe u

section General

variable {K P : Type u} [NontriviallyNormedField K]
  [NormedAddCommGroup P] [NormedSpace K P]

/-- Every diagonal of the ambient test series lies in the closed diagonal subspace. -/
theorem tensorTestSeries_apply_mem (n : ℕ) (x : P) :
    tensorTestSeries (K := K) n (fun _ => x) ∈ tensorTestSubmodule (K := K) (P := P) := by
  cases n with
  | zero =>
    rw [tensorTestSeries_zero]
    exact zero_mem _
  | succ m =>
    rw [tensorTestSubmodule, DependentCZero.mem_coordinateSubmodule]
    intro i
    change tensorTestCoordinate (K := K) (P := P) i
      (tensorTestSeries (K := K) (m + 1) (fun _ => x)) ∈ DiagonalSpan K P (i + 1)
    by_cases h : i = m
    · subst h
      rw [tensorTestSeries_coordinate]
      exact diagonalTensor_mem _ x
    · rw [tensorTestSeries_coordinate_ne i (m + 1) (by omega)]
      exact zero_mem _

/-- The tensor test map is `C^n` on the open unit ball as a map into the closed diagonal
subspace, for every `n : ℕ∞`. -/
theorem tensorTestMap_contDiffOn (n : ℕ∞) :
    ContDiffOn K n (tensorTestMap (K := K) (P := P)) (Metric.ball 0 1) :=
  contDiffOn_of_subtype _ isClosed_tensorTestSubmodule Metric.isOpen_ball
    (tensorTestMap_analyticOnNhd.contDiffOn Metric.isOpen_ball.uniqueDiffOn)

/-- A uniform factorial lower bound on projection norms excludes analyticity of the tensor test
map into the diagonal subspace at zero. -/
theorem not_analyticAt_tensorTestMap_of_factorial_le [CompleteSpace K] [CompleteSpace P]
    (hproj : ∀ n : ℕ, 1 ≤ n → ∀ R : TensorPower K P n →L[K] DiagonalSpan K P n,
      (∀ t : DiagonalSpan K P n, R (t : TensorPower K P n) = t) → (n.factorial : ℝ) ≤ ‖R‖) :
    ¬ AnalyticAt K (tensorTestMap (K := K) (P := P)) 0 := by
  intro ha
  obtain ⟨R, hR, C, r, -, -, hb⟩ := tensor_projections_of_analyticAt_tensorTestMap ha
  have hfac (m : ℕ) : ((m + 1).factorial : ℝ) ≤ C * r ^ (m + 1) :=
    (hproj (m + 1) (by omega) (R m)
      (fun t => by simpa using congrArg (fun L => L t) (hR m))).trans (hb m)
  have ht : Tendsto (fun n : ℕ => C * (r ^ n / (n.factorial : ℝ))) atTop (𝓝 0) := by
    simpa using (FloorSemiring.tendsto_pow_div_factorial_atTop r).const_mul C
  obtain ⟨N, hN⟩ := eventually_atTop.1 (ht.eventually (gt_mem_nhds zero_lt_one))
  have h1 := hN (N + 1) (by omega)
  have hpos : (0 : ℝ) < ((N + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  rw [← mul_div_assoc, div_lt_one hpos] at h1
  exact absurd (hfac N) (not_le.2 h1)

/-- The sInf form of Proposition G.4 gives the factorial lower bound for every projection. -/
theorem factorial_le_norm_of_sInf_eq {n : ℕ}
    (h : sInf {c : ℝ | ∃ R : TensorPower K P n →L[K] DiagonalSpan K P n,
        (∀ t : DiagonalSpan K P n, R (t : TensorPower K P n) = t) ∧ ‖R‖ = c} =
      (n.factorial : ℝ))
    (R : TensorPower K P n →L[K] DiagonalSpan K P n)
    (hR : ∀ t : DiagonalSpan K P n, R (t : TensorPower K P n) = t) :
    (n.factorial : ℝ) ≤ ‖R‖ := by
  rw [← h]
  exact csInf_le ⟨0, fun _ ⟨R, _, hc⟩ => hc ▸ norm_nonneg R⟩ ⟨R, hR, rfl⟩

end General

section L1

variable {K : Type u} [NontriviallyNormedField K]

/-- Every coefficient of the ambient test series on `ℓ¹(ℕ,K)` has a representative with values
in the diagonal subspace and with the same diagonal. -/
theorem exists_tensorTestSeries_lift (n : ℕ) :
    ∃ q : ContinuousMultilinearMap K (fun _ : Fin n => lp (fun _ : ℕ => K) 1)
        (tensorTestSubmodule (K := K) (P := lp (fun _ : ℕ => K) 1)),
      ∀ x, (q (fun _ => x) : tensorTestSpace K (lp (fun _ : ℕ => K) 1)) =
        tensorTestSeries (K := K) n (fun _ => x) := by
  obtain ⟨q, hq, -⟩ := L1PolynomialLift.exists_l1_diagonal_lift
    (tensorTestSubmodule (K := K) (P := lp (fun _ : ℕ => K) 1))
    isClosed_tensorTestSubmodule n (tensorTestSeries n) (tensorTestSeries_apply_mem n)
  exact ⟨q, hq⟩

/-- The diagonal-subspace-valued series of lifted coefficients. -/
def tensorTestLiftSeries :
    FormalMultilinearSeries K (lp (fun _ : ℕ => K) 1)
      (tensorTestSubmodule (K := K) (P := lp (fun _ : ℕ => K) 1)) :=
  fun n => (exists_tensorTestSeries_lift (K := K) n).choose

theorem coe_tensorTestLiftSeries_apply (n : ℕ) (x : lp (fun _ : ℕ => K) 1) :
    (tensorTestLiftSeries (K := K) n (fun _ => x) :
        tensorTestSpace K (lp (fun _ : ℕ => K) 1)) =
      tensorTestSeries (K := K) n (fun _ => x) :=
  (exists_tensorTestSeries_lift (K := K) n).choose_spec x

/-- The truncations of the tensor test map, entire polynomials into the diagonal subspace. -/
def tensorTestTruncation (N : ℕ) (x : lp (fun _ : ℕ => K) 1) :
    tensorTestSubmodule (K := K) (P := lp (fun _ : ℕ => K) 1) :=
  ∑ i ∈ Finset.range N, tensorTestLiftSeries (K := K) i (fun _ => x)

theorem coe_tensorTestTruncation (N : ℕ) (x : lp (fun _ : ℕ => K) 1) :
    (tensorTestTruncation (K := K) N x : tensorTestSpace K (lp (fun _ : ℕ => K) 1)) =
      (tensorTestSeries (K := K)).partialSum N x := by
  simp [tensorTestTruncation, FormalMultilinearSeries.partialSum,
    coe_tensorTestLiftSeries_apply]

/-- The truncations converge to the tensor test map uniformly on every closed ball of radius
less than one. -/
theorem tendstoUniformlyOn_tensorTestTruncation {r : ℝ} (hr : r < 1) :
    TendstoUniformlyOn (tensorTestTruncation (K := K)) (tensorTestMap (K := K))
      atTop (Metric.closedBall 0 r) := by
  let r' : ℝ≥0 := ⟨(max r 0 + 1) / 2, by positivity⟩
  have hcoe : (r' : ℝ) = (max r 0 + 1) / 2 := rfl
  have h0 := max_lt hr zero_lt_one
  have hr'1 : (r' : ℝ≥0∞) < 1 := by
    rw [ENNReal.coe_lt_one_iff, ← NNReal.coe_lt_coe, hcoe, NNReal.coe_one]
    linarith
  have hrr' : r < (r' : ℝ) := by
    rw [hcoe]
    linarith [le_max_left r 0]
  have hu := (tensorTestMap_hasFPowerSeriesOnBall (K := K)
    (P := lp (fun _ : ℕ => K) 1)).tendstoUniformlyOn hr'1
  have hu' := hu.mono (Metric.closedBall_subset_ball hrr')
  rw [Metric.tendstoUniformlyOn_iff] at hu' ⊢
  intro ε hε
  filter_upwards [hu' ε hε] with N hN x hx
  rw [Subtype.dist_eq, coe_tensorTestTruncation]
  simpa using hN x hx

end L1

end AlternatingAnalytic.PolynomialApproximation
