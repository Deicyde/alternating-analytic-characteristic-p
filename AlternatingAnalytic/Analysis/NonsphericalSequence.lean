import AlternatingAnalytic.Analysis.SphericalCompleteness
import Mathlib.Topology.Order.IsLUB

/-!
# Empty descending ball sequences

An ultrametric space fails to be spherically complete if and only if it has a sequence of nested
closed balls with strictly decreasing radii and empty intersection.
-/

open Metric Filter Topology

namespace AlternatingAnalytic

variable {Y : Type*} [MetricSpace Y] [IsUltrametricDist Y]

/-- A sequence of closed balls with strictly decreasing radii, each center in the previous
ball, and empty intersection. -/
def HasEmptyDescendingBallSequence (Y : Type*) [MetricSpace Y] : Prop :=
  ∃ (c : ℕ → Y) (r : ℕ → ℝ), StrictAnti r ∧
    (∀ n, dist (c (n + 1)) (c n) ≤ r n) ∧
    ¬ (⋂ n, closedBall (c n) (r n)).Nonempty

/-- An empty descending ball sequence rules out spherical completeness. -/
theorem HasEmptyDescendingBallSequence.not_sphericallyComplete
    (h : HasEmptyDescendingBallSequence Y) : ¬ SphericallyCompleteSpace Y := by
  classical
  intro hsc
  let : SphericallyCompleteSpace Y := hsc
  obtain ⟨c, r, hr, hstep, hempty⟩ := h
  have hr0 (n : ℕ) : 0 ≤ r n := dist_nonneg.trans (hstep n)
  have hnest : Antitone (fun n => closedBall (c n) (r n)) := by
    apply antitone_nat_of_succ_le
    intro n x hx
    exact (IsUltrametricDist.dist_triangle_max x (c (n + 1)) (c n)).trans
      (max_le ((mem_closedBall.mp hx).trans (hr.antitone (Nat.le_succ n))) (hstep n))
  let S : Set (Y × ℝ) := Set.range (fun n => (c n, r n))
  have hSne : S.Nonempty := ⟨(c 0, r 0), ⟨0, rfl⟩⟩
  have hmeet : ∀ p ∈ S, ∀ q ∈ S,
      (closedBall p.1 p.2 ∩ closedBall q.1 q.2).Nonempty := by
    rintro _ ⟨n, rfl⟩ _ ⟨m, rfl⟩
    have hc : c (max n m) ∈ closedBall (c (max n m)) (r (max n m)) := by
      simpa using hr0 (max n m)
    exact ⟨c (max n m), hnest (le_max_left n m) hc, hnest (le_max_right n m) hc⟩
  obtain ⟨x, hx⟩ := SphericallyCompleteSpace.inter_nonempty S hSne hmeet
  apply hempty
  refine ⟨x, Set.mem_iInter.mpr fun n => ?_⟩
  exact Set.mem_iInter.mp (Set.mem_iInter.mp hx (c n, r n)) ⟨n, rfl⟩

/-- A non-spherically-complete ultrametric space has an empty descending ball sequence. -/
theorem hasEmptyDescendingBallSequence_of_not_sphericallyComplete
    (h : ¬ SphericallyCompleteSpace Y) : HasEmptyDescendingBallSequence Y := by
  classical
  have hbad : ∃ S : Set (Y × ℝ), S.Nonempty ∧
      (∀ p ∈ S, ∀ q ∈ S, (closedBall p.1 p.2 ∩ closedBall q.1 q.2).Nonempty) ∧
      ¬ (⋂ p ∈ S, closedBall p.1 p.2).Nonempty := by
    by_contra! hn
    exact h ⟨hn⟩
  obtain ⟨S, hSne, hmeet, hempty⟩ := hbad
  have hr0 : ∀ p ∈ S, 0 ≤ p.2 := by
    intro p hp
    obtain ⟨z, hz, _⟩ := hmeet p hp p hp
    exact dist_nonneg.trans (mem_closedBall.mp hz)
  have hdist : ∀ p ∈ S, ∀ q ∈ S, dist p.1 q.1 ≤ max p.2 q.2 := by
    intro p hp q hq
    obtain ⟨z, hz, hw⟩ := hmeet p hp q hq
    exact (IsUltrametricDist.dist_triangle_max p.1 z q.1).trans
      (max_le_max (by simpa only [dist_comm] using mem_closedBall.mp hz)
        (mem_closedBall.mp hw))
  let R : Set ℝ := Prod.snd '' S
  have hRne : R.Nonempty := hSne.image Prod.snd
  have hRb : BddBelow R := ⟨0, by rintro _ ⟨p, hp, rfl⟩; exact hr0 p hp⟩
  have hnot : sInf R ∉ R := by
    rintro ⟨p, hp, heq⟩
    apply hempty
    refine ⟨p.1, ?_⟩
    simp only [Set.mem_iInter]
    intro q hq
    have hpq : p.2 ≤ q.2 := heq ▸ csInf_le hRb ⟨q, hq, rfl⟩
    exact (hdist p hp q hq).trans (max_le hpq le_rfl)
  obtain ⟨r, hr, _, hrlim, hrmem⟩ :=
    (isGLB_csInf hRne hRb).exists_seq_strictAnti_tendsto_of_notMem hnot hRne
  have hc : ∀ n, ∃ c : Y, (c, r n) ∈ S := by
    intro n
    obtain ⟨p, hp, heq⟩ := hrmem n
    exact ⟨p.1, by simpa only [← heq] using hp⟩
  choose c hc using hc
  refine ⟨c, r, hr, ?_, ?_⟩
  · intro n
    exact (hdist (c (n + 1), r (n + 1)) (hc (n + 1)) (c n, r n) (hc n)).trans
      (max_le (hr.antitone (Nat.le_succ n)) le_rfl)
  · rintro ⟨x, hx⟩
    apply hempty
    refine ⟨x, ?_⟩
    simp only [Set.mem_iInter] at hx ⊢
    intro p hp
    have hinf : sInf R < p.2 := lt_of_le_of_ne (csInf_le hRb ⟨p, hp, rfl⟩)
      (fun heq => hnot (heq ▸ (show p.2 ∈ R from ⟨p, hp, rfl⟩)))
    obtain ⟨n, hn⟩ := (hrlim.eventually (eventually_lt_nhds hinf)).exists
    have hxp : dist x (c n) ≤ p.2 := (mem_closedBall.mp (hx n)).trans hn.le
    have hcp : dist (c n) p.1 ≤ p.2 :=
      (hdist (c n, r n) (hc n) p hp).trans (max_le hn.le le_rfl)
    exact (IsUltrametricDist.dist_triangle_max x (c n) p.1).trans (max_le hxp hcp)

/-- An ultrametric space has an empty descending ball sequence if and only if it is not
spherically complete. -/
theorem hasEmptyDescendingBallSequence_iff :
    HasEmptyDescendingBallSequence Y ↔ ¬ SphericallyCompleteSpace Y :=
  ⟨HasEmptyDescendingBallSequence.not_sphericallyComplete,
    hasEmptyDescendingBallSequence_of_not_sphericallyComplete⟩

end AlternatingAnalytic
