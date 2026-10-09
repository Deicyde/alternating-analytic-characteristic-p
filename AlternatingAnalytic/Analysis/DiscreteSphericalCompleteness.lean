import AlternatingAnalytic.Analysis.SphericalCompleteness

/-!
# Discrete distances give spherical completeness

A complete ultrametric space whose nonzero distances lie in `e ^ ℤ` is spherically
complete (Lemma D.1, also used in the proof of Corollary 4.3).
-/

open Metric Filter Topology

namespace AlternatingAnalytic

variable {Y : Type*} [MetricSpace Y] [IsUltrametricDist Y] [CompleteSpace Y]

/-- Every complete ultrametric space whose nonzero distances are integral powers of
one real number greater than one is spherically complete. -/
theorem sphericallyCompleteSpace_of_discreteDist {e : ℝ} (he : 1 < e)
    (hval : ∀ x y : Y, x ≠ y → ∃ n : ℤ, dist x y = e ^ n) :
    SphericallyCompleteSpace Y := by
  classical
  constructor
  intro S hSne hmeet
  let : Nonempty Y := ⟨hSne.choose.1⟩
  -- radii are nonnegative
  have hrnn : ∀ p ∈ S, 0 ≤ p.2 := by
    intro p hp
    obtain ⟨z, hz, -⟩ := hmeet p hp p hp
    exact le_trans dist_nonneg (mem_closedBall.mp hz)
  -- centres are close
  have hdist : ∀ p ∈ S, ∀ q ∈ S, dist p.1 q.1 ≤ max p.2 q.2 := by
    intro p hp q hq
    obtain ⟨z, hz1, hz2⟩ := hmeet p hp q hq
    have h1 : dist p.1 z ≤ p.2 := by
      rw [dist_comm]; exact mem_closedBall.mp hz1
    have h2 : dist z q.1 ≤ q.2 := by
      exact mem_closedBall.mp hz2
    exact (IsUltrametricDist.dist_triangle_max p.1 z q.1).trans (max_le_max h1 h2)
  by_cases hcase : ∃ p ∈ S, ∀ q ∈ S, dist p.1 q.1 ≤ q.2
  · obtain ⟨p, hp, h⟩ := hcase
    refine ⟨p.1, ?_⟩
    simp only [Set.mem_iInter]
    intro q hq
    rw [mem_closedBall]
    exact h q hq
  · push Not at hcase
    -- If no centre lies in every ball, there is a strictly descending step.
    have step : ∀ p : Y × ℝ, p ∈ S → ∃ q, q ∈ S ∧ dist p.1 q.1 ≤ p.2 ∧ q.2 < dist p.1 q.1 := by
      intro p hp
      obtain ⟨q, hq, hlt⟩ := hcase p hp
      refine ⟨q, hq, ?_, hlt⟩
      have := hdist p hp q hq
      rcases max_cases p.2 q.2 with ⟨h, -⟩ | ⟨h, -⟩
      · rwa [h] at this
      · exact absurd (this.trans_eq h) (not_le.mpr hlt)
    choose! nxt hnxtS hnxt1 hnxt2 using step
    obtain ⟨p₀, hp₀⟩ := hSne
    set u : ℕ → Y × ℝ := fun n => Nat.rec p₀ (fun _ q => nxt q) n with hu
    have huS : ∀ n, u n ∈ S := by
      intro n; induction n with
      | zero => exact hp₀
      | succ n ih => exact hnxtS _ ih
    set d : ℕ → ℝ := fun n => dist (u n).1 (u (n + 1)).1 with hd
    have hd_le : ∀ n, d n ≤ (u n).2 := fun n => hnxt1 _ (huS n)
    have hd_gt : ∀ n, (u (n + 1)).2 < d n := fun n => hnxt2 _ (huS n)
    have hd_pos : ∀ n, 0 < d n := fun n => lt_of_le_of_lt (hrnn _ (huS (n + 1))) (hd_gt n)
    have hd_anti : ∀ n, d (n + 1) < d n := fun n => lt_of_le_of_lt (hd_le (n + 1)) (hd_gt n)
    have hd_mono : ∀ n m : ℕ, n ≤ m → d m ≤ d n := by
      intro n m h
      induction m with
      | zero => have hn : n = 0 := Nat.le_zero.mp h; subst hn; exact le_rfl
      | succ m ih =>
        rcases Nat.lt_or_ge n (m + 1) with hh | hh
        · exact le_trans (hd_anti m).le (ih (Nat.lt_succ_iff.mp hh))
        · have hn : n = m + 1 := le_antisymm h hh
          subst hn; exact le_rfl
    have hexp : ∀ n, ∃ k : ℤ, d n = e ^ k := by
      intro n
      refine hval (u n).1 (u (n + 1)).1 (fun h0 => ?_)
      have hz : d n = 0 := by simp [hd, h0]
      exact absurd hz (hd_pos n).ne'
    choose k hk using hexp
    have hk_anti : ∀ n, k (n + 1) < k n := by
      intro n
      have := hd_anti n
      rw [hk (n + 1), hk n] at this
      exact (zpow_lt_zpow_iff_right₀ he).mp this
    have hk_le : ∀ n, k n ≤ k 0 - n := by
      intro n; induction n with
      | zero => simp
      | succ n ih =>
        have := hk_anti n
        push_cast
        omega
    have he0 : (0:ℝ) < e := lt_trans zero_lt_one he
    have hd_tendsto : Tendsto d atTop (𝓝 0) := by
      have hbound : ∀ n : ℕ, d n ≤ (e ^ (k 0)) * (e⁻¹) ^ n := by
        intro n
        rw [hk n]
        have : k n ≤ k 0 - n := hk_le n
        calc e ^ (k n) ≤ e ^ (k 0 - (n:ℤ)) := by
              exact zpow_le_zpow_right₀ he.le this
          _ = (e ^ (k 0)) * (e⁻¹) ^ n := by
              rw [zpow_sub₀ (ne_of_gt he0)]
              simp [zpow_natCast, inv_pow, div_eq_mul_inv]
      have h1 : Tendsto (fun n : ℕ => (e ^ (k 0)) * (e⁻¹) ^ n) atTop (𝓝 0) := by
        have : Tendsto (fun n : ℕ => (e⁻¹) ^ n) atTop (𝓝 0) :=
          tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
            (by rw [inv_lt_one₀ he0]; exact he)
        simpa using this.const_mul (e ^ (k 0))
      exact squeeze_zero (fun n => (hd_pos n).le) hbound h1
    -- the centres form a Cauchy sequence
    have hchain : ∀ n m : ℕ, n ≤ m → dist (u n).1 (u m).1 ≤ d n := by
      intro n m hnm
      induction m with
      | zero =>
        have hn : n = 0 := Nat.le_zero.mp hnm
        subst hn; simpa using (hd_pos 0).le
      | succ m ih =>
        rcases Nat.lt_or_ge n (m + 1) with h | h
        · have hnm' : n ≤ m := Nat.lt_succ_iff.mp h
          have h1 := ih hnm'
          have h2 : dist (u m).1 (u (m + 1)).1 = d m := rfl
          exact (IsUltrametricDist.dist_triangle_max (u n).1 (u m).1 (u (m + 1)).1).trans
            (max_le h1 (by rw [h2]; exact hd_mono n m hnm'))
        · have hn : n = m + 1 := le_antisymm hnm h
          subst hn; simpa using (hd_pos (m + 1)).le
    have hcauchy : CauchySeq (fun n => (u n).1) := by
      refine cauchySeq_of_le_tendsto_0 d (fun n m N hn hm => ?_) hd_tendsto
      have h1 : dist (u N).1 (u n).1 ≤ d N := hchain N n hn
      have h2 : dist (u N).1 (u m).1 ≤ d N := hchain N m hm
      exact (IsUltrametricDist.dist_triangle_max (u n).1 (u N).1 (u m).1).trans
        (max_le (by simpa only [dist_comm] using h1) h2)
    obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcauchy
    refine ⟨x, ?_⟩
    simp only [Set.mem_iInter]
    intro q hq
    rw [mem_closedBall]
    by_contra hcon
    push Not at hcon
    have hpos : 0 < dist x q.1 := lt_of_le_of_lt (hrnn q hq) hcon
    have ha : Tendsto (fun n => dist x (u n).1) atTop (𝓝 0) := by
      have h := tendsto_iff_dist_tendsto_zero.mp hx
      simpa only [dist_comm] using h
    have hb : Tendsto (fun n => (u (n + 1)).2) atTop (𝓝 0) :=
      squeeze_zero (fun n => hrnn _ (huS (n + 1))) (fun n => (hd_gt n).le) hd_tendsto
    have hA : ∀ᶠ n in atTop, dist x (u n).1 < dist x q.1 := ha.eventually (eventually_lt_nhds hpos)
    have hB : ∀ᶠ n in atTop, (u (n + 1)).2 < dist x q.1 := hb.eventually (eventually_lt_nhds hpos)
    obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp hA
    obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.mp hB
    set j := max N1 N2 with hj
    have h1 : dist x (u (j + 1)).1 < dist x q.1 :=
      hN1 (j + 1) (le_trans (le_max_left N1 N2) (Nat.le_succ j))
    have h2 : (u (j + 1)).2 < dist x q.1 := hN2 j (le_max_right N1 N2)
    have h3 : dist (u (j + 1)).1 q.1 ≤ max ((u (j + 1)).2) q.2 :=
      hdist _ (huS (j + 1)) q hq
    have h4 : dist x q.1 ≤ max (dist x (u (j + 1)).1) (dist (u (j + 1)).1 q.1) := by
      exact IsUltrametricDist.dist_triangle_max x (u (j + 1)).1 q.1
    have h5 : max (dist x (u (j + 1)).1) (dist (u (j + 1)).1 q.1) < dist x q.1 :=
      max_lt h1 (lt_of_le_of_lt h3 (max_lt h2 hcon))
    exact absurd h4 (not_le.mpr h5)

/-- The same statement with distances in `r ^ ℤ` for `0 < r < 1`, as in Lemma D.1. -/
theorem sphericallyCompleteSpace_of_discreteDist_radius {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1)
    (hval : ∀ x y : Y, x ≠ y → ∃ n : ℤ, dist x y = r ^ n) :
    SphericallyCompleteSpace Y := by
  apply sphericallyCompleteSpace_of_discreteDist ((one_lt_inv₀ hr0).mpr hr1)
  intro x y hxy
  obtain ⟨n, hn⟩ := hval x y hxy
  exact ⟨-n, by simpa [zpow_neg] using hn⟩

end AlternatingAnalytic
