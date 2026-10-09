/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
import AlternatingAnalytic.Coordinates.WeightedNorm.Model

/-!
# The weighted norm is not spherically complete

Over an ultrametric normed field `𝕜`, let `a_n = ∑_{j<n} e_j ∈ C₀(ℕ, 𝕜)` and let
`B_n = {x | ‖x - a_n‖_w ≤ w_n}`. These balls are nonempty and nested, but a common point `x`
would satisfy `|x_j - 1| < 1`, hence `|x_j| = 1`, for every `j`, contradicting `x_j → 0`.
Hence no model of the weighted norm (`Model.lean`) is spherically complete (Remark I.3).
-/

set_option backward.isDefEq.respectTransparency false

open Filter Topology Metric
open scoped ZeroAtInfty

namespace AlternatingAnalytic.WeightedNorm

variable {𝕜 : Type*} [NormedField 𝕜]

variable (𝕜) in
/-- The null sequence `a_n = ∑_{j<n} e_j`. -/
noncomputable def partialOnes (n : ℕ) : C₀(ℕ, 𝕜) where
  toFun j := if j < n then 1 else 0
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    rw [cocompact_eq_cofinite, Nat.cofinite_eq_atTop]
    exact tendsto_const_nhds.congr'
      (eventually_atTop.2 ⟨n, fun j hj => by simp [not_lt.2 hj]⟩)

theorem partialOnes_apply (n j : ℕ) : partialOnes 𝕜 n j = if j < n then 1 else 0 := rfl

variable (𝕜) in
/-- The closed weighted ball `B_n = B̄_w(a_n, w_n)`. -/
def ball (n : ℕ) : Set C₀(ℕ, 𝕜) :=
  {x | (⨆ j : ℕ, weight j * ‖x j - (if j < n then (1 : 𝕜) else 0)‖) ≤ weight n}

theorem mem_ball_iff_wNorm {n : ℕ} {x : C₀(ℕ, 𝕜)} :
    x ∈ ball 𝕜 n ↔ wNorm (x - partialOnes 𝕜 n) ≤ weight n := Iff.rfl

theorem mem_ball_iff {n : ℕ} {x : C₀(ℕ, 𝕜)} :
    x ∈ ball 𝕜 n ↔ ∀ j, weight j * ‖x j - (if j < n then (1 : 𝕜) else 0)‖ ≤ weight n :=
  mem_ball_iff_wNorm.trans wNorm_le_iff

theorem partialOnes_mem_ball (n : ℕ) : partialOnes 𝕜 n ∈ ball 𝕜 n :=
  mem_ball_iff.2 fun j => by
    rw [partialOnes_apply, sub_self, norm_zero, mul_zero]
    exact (weight_pos n).le

variable [IsUltrametricDist 𝕜]

theorem norm_le_one_of_norm_sub_one_lt {a : 𝕜} (h : ‖a - 1‖ < 1) : ‖a‖ ≤ 1 := by
  have := IsUltrametricDist.norm_add_le_max (a - 1) 1
  rw [sub_add_cancel, norm_one] at this
  exact this.trans (max_le h.le le_rfl)

theorem norm_eq_one_of_norm_sub_one_lt {a : 𝕜} (h : ‖a - 1‖ < 1) : ‖a‖ = 1 := by
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := a - 1) (y := 1)
    (by rw [norm_one]; exact h.ne)
  rw [sub_add_cancel, norm_one, max_eq_right h.le] at this
  exact this

omit [IsUltrametricDist 𝕜] in
theorem norm_sub_one_lt_of_mem_ball_succ {n : ℕ} {x : C₀(ℕ, 𝕜)} (hx : x ∈ ball 𝕜 (n + 1)) :
    ‖x n - 1‖ < 1 := by
  have h := mem_ball_iff.1 hx n
  simp only [Nat.lt_add_one, ↓reduceIte] at h
  by_contra hc
  have : weight n ≤ weight n * ‖x n - 1‖ := le_mul_of_one_le_right (weight_pos n).le (not_lt.1 hc)
  exact absurd (this.trans h) (not_le.2 (weight_succ_lt n))

theorem ball_succ_subset (n : ℕ) : ball 𝕜 (n + 1) ⊆ ball 𝕜 n := by
  intro x hx
  refine mem_ball_iff.2 fun j => ?_
  rcases eq_or_ne j n with rfl | hjn
  · simp only [lt_irrefl, ↓reduceIte, sub_zero]
    exact mul_le_of_le_one_right (weight_pos j).le
      (norm_le_one_of_norm_sub_one_lt (norm_sub_one_lt_of_mem_ball_succ hx))
  · have h := mem_ball_iff.1 hx j
    have hiff : (j < n + 1) ↔ (j < n) := by omega
    simp only [hiff] at h
    exact h.trans (weight_succ_le n)

theorem ball_antitone : Antitone (ball 𝕜) := antitone_nat_of_succ_le ball_succ_subset

theorem iInter_ball_eq_empty : (⋂ n, ball 𝕜 n) = ∅ := by
  ext x
  simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
  intro hx
  have hone : ∀ j, ‖x j‖ = 1 := fun j =>
    norm_eq_one_of_norm_sub_one_lt (norm_sub_one_lt_of_mem_ball_succ (hx (j + 1)))
  have hev : ∀ᶠ j in cofinite, ‖x j‖ < 1 := by
    have h := (tendsto_cofinite x).norm
    rw [norm_zero] at h
    exact h.eventually (gt_mem_nhds one_pos)
  obtain ⟨j, hj⟩ := hev.exists
  exact (lt_irrefl (1 : ℝ)) (hone j ▸ hj)

/-- The weighted balls are nonempty, nested, and have empty intersection. -/
theorem ball_family :
    (∀ n, (ball 𝕜 n).Nonempty) ∧ (∀ n, ball 𝕜 (n + 1) ⊆ ball 𝕜 n) ∧
      (⋂ n, ball 𝕜 n) = ∅ :=
  ⟨fun n => ⟨_, partialOnes_mem_ball n⟩, ball_succ_subset, iInter_ball_eq_empty⟩

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] (e : G ≃ₗ[𝕜] C₀(ℕ, 𝕜))

theorem model_mem_closedBall_iff (he : ∀ g, ‖g‖ = wNorm (e g)) (n : ℕ) (g : G) :
    g ∈ closedBall (e.symm (partialOnes 𝕜 n)) (weight n) ↔ e g ∈ ball 𝕜 n := by
  rw [mem_closedBall, dist_eq_norm, he, map_sub, LinearEquiv.apply_symm_apply]
  exact mem_ball_iff_wNorm.symm

/-- No model of the weighted norm is spherically complete. -/
theorem model_not_sphericallyCompleteSpace (he : ∀ g, ‖g‖ = wNorm (e g)) :
    ¬ SphericallyCompleteSpace G := by
  intro hG
  let S : Set (G × ℝ) := Set.range fun n => (e.symm (partialOnes 𝕜 n), weight n)
  obtain ⟨g, hg⟩ := hG.inter_nonempty S ⟨_, 0, rfl⟩ (by
    rintro _ ⟨n, rfl⟩ _ ⟨m, rfl⟩
    refine ⟨e.symm (partialOnes 𝕜 (max n m)), ?_, ?_⟩
    · rw [model_mem_closedBall_iff e he, LinearEquiv.apply_symm_apply]
      exact ball_antitone (le_max_left n m) (partialOnes_mem_ball _)
    · rw [model_mem_closedBall_iff e he, LinearEquiv.apply_symm_apply]
      exact ball_antitone (le_max_right n m) (partialOnes_mem_ball _))
  have hmem : e g ∈ ⋂ n, ball 𝕜 n := by
    refine Set.mem_iInter.2 fun n => ?_
    have := Set.mem_iInter₂.1 hg (e.symm (partialOnes 𝕜 n), weight n) ⟨n, rfl⟩
    exact (model_mem_closedBall_iff e he n g).1 this
  rw [iInter_ball_eq_empty] at hmem
  exact hmem

end AlternatingAnalytic.WeightedNorm
