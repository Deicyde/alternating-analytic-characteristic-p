import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Max

/-! The finite maximum used in the Laurent constant-coefficient support estimate. -/

open Filter Topology

namespace AlternatingAnalytic

/-- The positive geometric weight sequence has an attained maximum. -/
theorem exists_geometricWeight_max {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ n : ℕ, 1 ≤ ((n : ℝ) + 1) * r ^ n ∧
      ∀ m : ℕ, ((m : ℝ) + 1) * r ^ m ≤ ((n : ℝ) + 1) * r ^ n := by
  have ht : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * r ^ n) atTop (𝓝 0) := by
    simpa [add_mul] using
      (tendsto_self_mul_const_pow_of_lt_one hr0 hr1).add
        (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (eventually_lt_nhds zero_lt_one))
  obtain ⟨n, hn, hmax⟩ := (Finset.range (N + 1)).exists_max_image
    (fun n : ℕ => ((n : ℝ) + 1) * r ^ n) ⟨0, by simp⟩
  have hpos : 1 ≤ ((n : ℝ) + 1) * r ^ n := by
    simpa using hmax 0 (by simp)
  refine ⟨n, hpos, fun m => ?_⟩
  by_cases hm : m < N + 1
  · exact hmax m (Finset.mem_range.mpr hm)
  · exact (hN m (by omega)).le.trans hpos

/-- At radii at most one half, every geometric weight is at most one. -/
theorem geometricWeight_le_one {r : ℝ} (hr0 : 0 ≤ r) (hrhalf : r ≤ 1 / 2)
    (n : ℕ) : ((n : ℝ) + 1) * r ^ n ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hn : (n : ℝ) + 2 ≤ 2 * ((n : ℝ) + 1) := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
      have hpow : 0 ≤ r ^ n := pow_nonneg hr0 _
      calc
        (((n + 1 : ℕ) : ℝ) + 1) * r ^ (n + 1)
            = (((n : ℝ) + 2) * r) * r ^ n := by
                push_cast
                rw [pow_succ]
                ring
        _ ≤ ((n : ℝ) + 1) * r ^ n := by
              apply mul_le_mul_of_nonneg_right _ hpow
              nlinarith
        _ ≤ 1 := ih

end AlternatingAnalytic
