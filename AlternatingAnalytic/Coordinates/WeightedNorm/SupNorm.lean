/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import AlternatingAnalytic.Analysis.DiscreteSphericalCompleteness
import AlternatingAnalytic.Analysis.DiscreteTargetAnalytic
import AlternatingAnalytic.Analysis.LaurentField

/-!
# The supremum norm on null sequences

For the space `C₀(ℕ, β)` of null sequences with its supremum norm we show that the norm of a
sequence is attained at some coordinate, that the norm is ultrametric when `β` is, and, over the
Laurent field `κ((t))` with `‖t‖ = r`, that nonzero norms lie in `r^ℤ`, so that the space is
spherically complete. We also record that precomposition on continuous alternating maps into any
complete ultrametric space over `κ((t))` is analytic (Remark I.3 of the paper).
-/

set_option backward.isDefEq.respectTransparency false

open Filter Topology
open scoped ZeroAtInfty NNReal

namespace AlternatingAnalytic.WeightedNorm

section General

variable {β : Type*} [NormedAddCommGroup β]

/-- Each coordinate of a null sequence is bounded by its supremum norm. -/
theorem norm_apply_le (x : C₀(ℕ, β)) (j : ℕ) : ‖x j‖ ≤ ‖x‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  exact x.toBCF.norm_coe_le_norm j

/-- A coordinatewise bound bounds the supremum norm. -/
theorem norm_le_of_forall {x : C₀(ℕ, β)} {C : ℝ} (hC : 0 ≤ C) (h : ∀ j, ‖x j‖ ≤ C) :
    ‖x‖ ≤ C := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  exact (BoundedContinuousFunction.norm_le hC).2 h

/-- A null sequence on `ℕ` tends to zero along the cofinite filter. -/
theorem tendsto_cofinite (x : C₀(ℕ, β)) : Tendsto (fun j => x j) cofinite (𝓝 0) := by
  have := x.zero_at_infty'
  rwa [cocompact_eq_cofinite] at this

/-- The supremum norm of a null sequence is attained at some coordinate. -/
theorem exists_norm_eq (x : C₀(ℕ, β)) : ∃ j, ‖x‖ = ‖x j‖ := by
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  have : ∃ j₀, x j₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (ZeroAtInftyContinuousMap.ext h)
  obtain ⟨j₀, hj₀⟩ := this
  have hpos : 0 < ‖x j₀‖ := norm_pos_iff.2 hj₀
  have hev : ∀ᶠ j in cofinite, ‖x j‖ < ‖x j₀‖ := by
    have h := (tendsto_cofinite x).norm
    rw [norm_zero] at h
    exact h.eventually (gt_mem_nhds hpos)
  have hfin : {j | ‖x j₀‖ ≤ ‖x j‖}.Finite := by
    simpa [not_lt] using Filter.eventually_cofinite.1 hev
  obtain ⟨j, hj, hmax⟩ := hfin.toFinset.exists_max_image (fun j => ‖x j‖) ⟨j₀, by simp⟩
  refine ⟨j, le_antisymm (norm_le_of_forall (norm_nonneg _) fun i => ?_) (norm_apply_le x j)⟩
  by_cases hi : ‖x j₀‖ ≤ ‖x i‖
  · exact hmax i (by simpa using hi)
  · exact (not_le.1 hi).le.trans (by simpa using hj)

/-- The supremum norm is ultrametric when the coefficient norm is. -/
theorem norm_add_le_max [IsUltrametricDist β] (x y : C₀(ℕ, β)) :
    ‖x + y‖ ≤ max ‖x‖ ‖y‖ :=
  norm_le_of_forall (le_max_of_le_left (norm_nonneg _)) fun j =>
    (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le_max (norm_apply_le x j) (norm_apply_le y j))

/-- `C₀(ℕ, β)` is ultrametric when `β` is. -/
theorem isUltrametricDist [IsUltrametricDist β] : IsUltrametricDist C₀(ℕ, β) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm norm_add_le_max

end General

section Laurent

variable (κ : Type*) [Field κ] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)]

/-- The nonzero norms of `κ((t))` are exactly the integral powers of `r`. -/
theorem range_norm_units :
    Set.range (fun c : (LaurentField κ r)ˣ => ‖(c : LaurentField κ r)‖) =
      Set.range (fun n : ℤ => (r : ℝ) ^ n) := by
  ext a
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨_, (LaurentField.norm_of_ne_zero κ r _ c.ne_zero).symm⟩
  · rintro ⟨n, rfl⟩
    let y : LaurentField κ r := (HahnSeries.single n (1 : κ) : LaurentSeries κ)
    have hy : y ≠ 0 := by
      change (HahnSeries.single n (1 : κ) : LaurentSeries κ) ≠ 0
      exact HahnSeries.single_ne_zero one_ne_zero
    refine ⟨Units.mk0 y hy, ?_⟩
    change ‖y‖ = _
    rw [LaurentField.norm_of_ne_zero κ r y hy]
    change (r : ℝ) ^ (HahnSeries.single n (1 : κ) : LaurentSeries κ).order = _
    rw [HahnSeries.order_single one_ne_zero]

/-- Nonzero supremum norms of null sequences in `κ((t))` are integral powers of `r`. -/
theorem norm_mem_zpowers (x : C₀(ℕ, LaurentField κ r)) (hx : x ≠ 0) :
    ∃ n : ℤ, ‖x‖ = (r : ℝ) ^ n := by
  obtain ⟨j, hj⟩ := exists_norm_eq x
  have hxj : x j ≠ 0 := by
    intro h
    rw [h, norm_zero, norm_eq_zero] at hj
    exact hx hj
  exact ⟨_, hj.trans (LaurentField.norm_of_ne_zero κ r _ hxj)⟩

/-- `c₀(ℕ, κ((t)))` with its supremum norm is spherically complete. -/
theorem sphericallyCompleteSpace : SphericallyCompleteSpace C₀(ℕ, LaurentField κ r) := by
  have := isUltrametricDist (β := LaurentField κ r)
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (Fact.out : 0 < r)
  have hr1 : (r : ℝ) < 1 := by exact_mod_cast (Fact.out : r < 1)
  apply sphericallyCompleteSpace_of_discreteDist_radius hr0 hr1
  intro x y hxy
  rw [dist_eq_norm]
  exact norm_mem_zpowers κ r _ (sub_ne_zero.2 hxy)

/-- Precomposition on degree-`k` continuous alternating maps into a complete ultrametric space
over `κ((t))` is analytic at every point, for all normed `E, E'`. -/
theorem analyticAt_compContinuousLinearMapCLM {E E' F : Type*}
    [NormedAddCommGroup E] [NormedSpace (LaurentField κ r) E]
    [NormedAddCommGroup E'] [NormedSpace (LaurentField κ r) E']
    [NormedAddCommGroup F] [NormedSpace (LaurentField κ r) F] [CompleteSpace F]
    (hF : ∀ x y : F, ‖x + y‖ ≤ max ‖x‖ ‖y‖) (k : ℕ) (f₀ : E →L[LaurentField κ r] E') :
    AnalyticAt (LaurentField κ r)
      (fun f : E →L[LaurentField κ r] E' =>
        (ContinuousAlternatingMap.compContinuousLinearMapCLM f :
          (E' [⋀^Fin k]→L[LaurentField κ r] F) →L[LaurentField κ r]
            (E [⋀^Fin k]→L[LaurentField κ r] F))) f₀ := by
  have hq : HasEquivalentUltrametricNorm (LaurentField κ r) F :=
    ⟨normSeminorm (LaurentField κ r) F, hF, ⟨1, one_pos, fun x => by simp⟩,
      ⟨1, one_pos, fun x => by simp⟩⟩
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (Fact.out : 0 < r)
  have hr1 : (r : ℝ) < 1 := by exact_mod_cast (Fact.out : r < 1)
  exact analyticAt_of_equivalentUltrametricNorm_discreteValueGroup (ι := Fin k) hq hr0 hr1
    (range_norm_units κ r) f₀

end Laurent

end AlternatingAnalytic.WeightedNorm
