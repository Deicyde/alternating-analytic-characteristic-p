/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
import AlternatingAnalytic.Coordinates.WeightedNorm.SupNorm

/-!
# The weighted norm on null sequences

The weighted norm `‖x‖_w = sup_j w_j ‖x_j‖` on `C₀(ℕ, β)`, with weights `w_j = 1 + 1/(j+2)`,
from Remark I.3. It is a norm with `‖x‖_∞ ≤ ‖x‖_w ≤ (3/2)‖x‖_∞`, ultrametric when `β` is.
`WeightedC0 β` is a type synonym of `C₀(ℕ, β)` carrying this norm.
-/

set_option backward.isDefEq.respectTransparency false

open Filter Topology
open scoped ZeroAtInfty NNReal

namespace AlternatingAnalytic.WeightedNorm

/-- The weights `w_j = 1 + 1/(j+2)`. -/
noncomputable def weight (j : ℕ) : ℝ := 1 + 1 / ((j : ℝ) + 2)

theorem one_le_weight (j : ℕ) : 1 ≤ weight j := by
  unfold weight
  have : 0 ≤ 1 / ((j : ℝ) + 2) := by positivity
  linarith

theorem weight_pos (j : ℕ) : 0 < weight j := lt_of_lt_of_le one_pos (one_le_weight j)

theorem weight_le (j : ℕ) : weight j ≤ 3 / 2 := by
  unfold weight
  have h : 1 / ((j : ℝ) + 2) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
  linarith

theorem weight_succ_lt (n : ℕ) : weight (n + 1) < weight n := by
  unfold weight
  have h : 1 / (((n + 1 : ℕ) : ℝ) + 2) < 1 / ((n : ℝ) + 2) :=
    one_div_lt_one_div_of_lt (by positivity) (by push_cast; linarith)
  linarith

theorem weight_succ_le (n : ℕ) : weight (n + 1) ≤ weight n := (weight_succ_lt n).le

section Norm

variable {β : Type*} [NormedAddCommGroup β]

/-- The weighted norm `‖x‖_w = sup_j w_j ‖x_j‖` of a null sequence. -/
noncomputable def wNorm (x : C₀(ℕ, β)) : ℝ := ⨆ j : ℕ, weight j * ‖x j‖

theorem bddAbove_weighted (x : C₀(ℕ, β)) :
    BddAbove (Set.range fun j => weight j * ‖x j‖) :=
  ⟨3 / 2 * ‖x‖, by
    rintro _ ⟨j, rfl⟩
    exact mul_le_mul (weight_le j) (norm_apply_le x j) (norm_nonneg _) (by norm_num)⟩

theorem le_wNorm (x : C₀(ℕ, β)) (j : ℕ) : weight j * ‖x j‖ ≤ wNorm x :=
  le_ciSup (bddAbove_weighted x) j

theorem wNorm_le_iff {x : C₀(ℕ, β)} {C : ℝ} : wNorm x ≤ C ↔ ∀ j, weight j * ‖x j‖ ≤ C :=
  ⟨fun h j => (le_wNorm x j).trans h, ciSup_le⟩

/-- The supremum norm is at most the weighted norm. -/
theorem norm_le_wNorm (x : C₀(ℕ, β)) : ‖x‖ ≤ wNorm x := by
  have h0 : 0 ≤ wNorm x :=
    (mul_nonneg (weight_pos 0).le (norm_nonneg _)).trans (le_wNorm x 0)
  exact norm_le_of_forall h0 fun j =>
    (le_mul_of_one_le_left (norm_nonneg _) (one_le_weight j)).trans (le_wNorm x j)

theorem wNorm_nonneg (x : C₀(ℕ, β)) : 0 ≤ wNorm x := (norm_nonneg x).trans (norm_le_wNorm x)

/-- The weighted norm is at most `3/2` times the supremum norm. -/
theorem wNorm_le (x : C₀(ℕ, β)) : wNorm x ≤ 3 / 2 * ‖x‖ :=
  wNorm_le_iff.2 fun j =>
    mul_le_mul (weight_le j) (norm_apply_le x j) (norm_nonneg _) (by norm_num)

theorem wNorm_add_le (x y : C₀(ℕ, β)) : wNorm (x + y) ≤ wNorm x + wNorm y :=
  wNorm_le_iff.2 fun j => by
    calc weight j * ‖(x + y) j‖ ≤ weight j * (‖x j‖ + ‖y j‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) (weight_pos j).le
      _ = weight j * ‖x j‖ + weight j * ‖y j‖ := mul_add _ _ _
      _ ≤ wNorm x + wNorm y := add_le_add (le_wNorm x j) (le_wNorm y j)

/-- The weighted norm is ultrametric when the coefficient norm is. -/
theorem wNorm_add_le_max [IsUltrametricDist β] (x y : C₀(ℕ, β)) :
    wNorm (x + y) ≤ max (wNorm x) (wNorm y) :=
  wNorm_le_iff.2 fun j => by
    calc weight j * ‖(x + y) j‖ ≤ weight j * max ‖x j‖ ‖y j‖ :=
          mul_le_mul_of_nonneg_left (IsUltrametricDist.norm_add_le_max _ _) (weight_pos j).le
      _ = max (weight j * ‖x j‖) (weight j * ‖y j‖) := mul_max_of_nonneg _ _ (weight_pos j).le
      _ ≤ max (wNorm x) (wNorm y) := max_le_max (le_wNorm x j) (le_wNorm y j)

theorem wNorm_eq_zero_iff (x : C₀(ℕ, β)) : wNorm x = 0 ↔ x = 0 := by
  constructor
  · intro h
    exact norm_le_zero_iff.1 ((norm_le_wNorm x).trans h.le)
  · rintro rfl
    exact le_antisymm (by simpa using wNorm_le (0 : C₀(ℕ, β))) (wNorm_nonneg _)

theorem wNorm_smul {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 β] (c : 𝕜) (x : C₀(ℕ, β)) :
    wNorm (c • x) = ‖c‖ * wNorm x := by
  unfold wNorm
  rw [Real.mul_iSup_of_nonneg (norm_nonneg c)]
  congr 1
  funext j
  rw [ZeroAtInftyContinuousMap.smul_apply, norm_smul]
  ring

end Norm

/-- A copy of `C₀(ℕ, β)` that carries the weighted norm. -/
def WeightedC0 (β : Type*) [NormedAddCommGroup β] : Type _ := C₀(ℕ, β)

namespace WeightedC0

variable (𝕜 β : Type*) [NormedField 𝕜] [NormedAddCommGroup β] [NormedSpace 𝕜 β]

instance : AddCommGroup (WeightedC0 β) := inferInstanceAs (AddCommGroup C₀(ℕ, β))

instance : Module 𝕜 (WeightedC0 β) := inferInstanceAs (Module 𝕜 C₀(ℕ, β))

/-- The algebraic identification of the weighted copy with `C₀(ℕ, β)`. -/
def equiv : WeightedC0 β ≃ₗ[𝕜] C₀(ℕ, β) := LinearEquiv.refl 𝕜 _

theorem wNorm_neg (x : C₀(ℕ, β)) : wNorm (-x) = wNorm x := by
  unfold wNorm
  simp only [ZeroAtInftyContinuousMap.neg_apply, norm_neg]

/-- The weighted norm as an additive group norm. -/
noncomputable def addGroupNorm : AddGroupNorm (WeightedC0 β) where
  toFun x := wNorm (show C₀(ℕ, β) from x)
  map_zero' := (wNorm_eq_zero_iff (0 : C₀(ℕ, β))).2 rfl
  add_le' x y := wNorm_add_le (show C₀(ℕ, β) from x) (show C₀(ℕ, β) from y)
  neg' x := wNorm_neg β (show C₀(ℕ, β) from x)
  eq_zero_of_map_eq_zero' x h := (wNorm_eq_zero_iff (show C₀(ℕ, β) from x)).1 h

/-- The weighted norm as a normed group structure. -/
noncomputable instance normedAddCommGroup : NormedAddCommGroup (WeightedC0 β) :=
  (addGroupNorm β).toNormedAddCommGroup

theorem norm_def (x : WeightedC0 β) : ‖x‖ = wNorm (show C₀(ℕ, β) from x) := rfl

noncomputable instance normedSpace : NormedSpace 𝕜 (WeightedC0 β) where
  norm_smul_le c x := (wNorm_smul c (show C₀(ℕ, β) from x)).le

/-- The norm of the weighted copy is the weighted norm of its image in `C₀(ℕ, β)`. -/
theorem norm_eq (x : WeightedC0 β) : ‖x‖ = wNorm (equiv 𝕜 β x) := rfl

end WeightedC0

end AlternatingAnalytic.WeightedNorm
