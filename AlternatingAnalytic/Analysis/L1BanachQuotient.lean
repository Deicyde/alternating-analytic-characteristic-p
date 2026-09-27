import AlternatingAnalytic.Analysis.L1Coordinates
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# The ordinary ℓ¹ quotient indexed by the closed unit ball

The quotient is the degree-one bounded-array construction. Scalar integer powers give
single-coordinate lifts with an explicit norm bound, which also proves openness directly.
The original sum norm on `lp` and the original norm on the output are used throughout.
-/

open scoped lp BigOperators

noncomputable section

namespace AlternatingAnalytic

/-- The closed unit ball, used as the coordinate index of the ordinary ℓ¹ quotient. -/
abbrev L1UnitBallIndex (H : Type*) [NormedAddCommGroup H] := {h : H // ‖h‖ ≤ 1}

variable (K H : Type*) [NontriviallyNormedField K]
  [NormedAddCommGroup H] [NormedSpace K H] [CompleteSpace H]

local instance : DecidableEq (L1UnitBallIndex H) := Classical.decEq _

/-- Synthesis of the closed-unit-ball coefficients by the degree-one bounded-array map. -/
def unitBallL1Quotient : lp (fun _ : L1UnitBallIndex H => K) 1 →L[K] H :=
  continuousMultilinearCurryFin1 K (lp (fun _ : L1UnitBallIndex H => K) 1) H
    (L1Coordinates.continuousMultilinearOfBounded
      (fun v : Fin 1 → L1UnitBallIndex H => (v 0 : H)) 1 (fun v => (v 0).property))

variable {K H}

/-- The quotient is the actual unconditional sum of its coordinate contributions. -/
theorem unitBallL1Quotient_hasSum (a : lp (fun _ : L1UnitBallIndex H => K) 1) :
    HasSum (fun v : L1UnitBallIndex H => a v • (v : H)) (unitBallL1Quotient K H a) := by
  have hs := L1Coordinates.continuousMultilinearOfBounded_hasSum
    (K := K) (fun v : Fin 1 → L1UnitBallIndex H => (v 0 : H)) 1
    (fun v => (v 0).property) (Fin.snoc 0 a)
  apply (Equiv.funUnique (Fin 1) (L1UnitBallIndex H)).hasSum_iff.mp
  simpa [unitBallL1Quotient, continuousMultilinearCurryFin1_apply, Function.comp_def] using hs

theorem unitBallL1Quotient_apply (a : lp (fun _ : L1UnitBallIndex H => K) 1) :
    unitBallL1Quotient K H a = ∑' v : L1UnitBallIndex H, a v • (v : H) :=
  (unitBallL1Quotient_hasSum a).tsum_eq.symm

/-- The synthesis map has operator norm at most one. -/
theorem norm_unitBallL1Quotient_le : ‖unitBallL1Quotient K H‖ ≤ 1 := by
  rw [unitBallL1Quotient, LinearIsometryEquiv.norm_map]
  exact L1Coordinates.continuousMultilinearOfBounded_norm_le _ 1 zero_le_one _

/-- A single coordinate maps to the indicated scalar multiple of its unit-ball index. -/
@[simp]
theorem unitBallL1Quotient_single (v : L1UnitBallIndex H) (a : K) :
    unitBallL1Quotient K H (lp.single 1 v a) = a • (v : H) := by
  classical
  rw [unitBallL1Quotient_apply, tsum_eq_single v]
  · simp
  · intro w hw
    rw [lp.single_apply_ne _ _ _ hw, zero_smul]

/-- Every nonzero output has a single-coordinate lift with the strict scalar bound. -/
theorem unitBallL1Quotient_exists_single_lt (c : K) (hc : 1 < ‖c‖)
    (h : H) (hh : h ≠ 0) :
    ∃ v : L1UnitBallIndex H, ∃ a : K,
      unitBallL1Quotient K H (lp.single 1 v a) = h ∧
      ‖lp.single (E := fun _ : L1UnitBallIndex H => K) 1 v a‖ < ‖c‖ * ‖h‖ := by
  have hcpos : 0 < ‖c‖ := zero_lt_one.trans hc
  have hcne : c ≠ 0 := norm_pos_iff.mp hcpos
  obtain ⟨n, hnlt, hnle⟩ := exists_mem_Ioc_zpow (norm_pos_iff.mpr hh) hc
  let a : K := c ^ (n + 1)
  have ha : a ≠ 0 := zpow_ne_zero _ hcne
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hnorm : ‖h‖ ≤ ‖a‖ := by simpa only [a, norm_zpow] using hnle
  have hv : ‖a⁻¹ • h‖ ≤ 1 := by
    rw [norm_smul, norm_inv, ← div_eq_inv_mul]
    exact (div_le_one hapos).mpr hnorm
  refine ⟨⟨a⁻¹ • h, hv⟩, a, ?_, ?_⟩
  · rw [unitBallL1Quotient_single]
    simp [smul_smul, ha]
  · rw [lp.norm_single (show (0 : ENNReal) < 1 by norm_num)]
    change ‖c ^ (n + 1)‖ < ‖c‖ * ‖h‖
    rw [norm_zpow]
    calc
      ‖c‖ ^ (n + 1) = ‖c‖ * ‖c‖ ^ n := by
        rw [zpow_add₀ hcpos.ne', zpow_one, mul_comm]
      _ < ‖c‖ * ‖h‖ := mul_lt_mul_of_pos_left hnlt hcpos

/-- The non-strict single-coordinate estimate also includes the zero output. -/
theorem unitBallL1Quotient_exists_single_le (c : K) (hc : 1 < ‖c‖) (h : H) :
    ∃ v : L1UnitBallIndex H, ∃ a : K,
      unitBallL1Quotient K H (lp.single 1 v a) = h ∧
      ‖lp.single (E := fun _ : L1UnitBallIndex H => K) 1 v a‖ ≤ ‖c‖ * ‖h‖ := by
  by_cases hh : h = 0
  · subst h
    exact ⟨⟨0, by simp⟩, 0, by simp⟩
  · obtain ⟨v, a, hqa, ha⟩ := unitBallL1Quotient_exists_single_lt c hc h hh
    exact ⟨v, a, hqa, ha.le⟩

/-- The unit-ball synthesis map is onto, including when the output space is trivial. -/
theorem unitBallL1Quotient_surjective : Function.Surjective (unitBallL1Quotient K H) := by
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm K
  intro h
  obtain ⟨v, a, hqa, _⟩ := unitBallL1Quotient_exists_single_le c hc h
  exact ⟨lp.single 1 v a, hqa⟩

/-- The lifting estimate gives an explicit ball contained in each ball image. -/
theorem unitBallL1Quotient_ball_subset (c : K) (hc : 1 < ‖c‖)
    (x : lp (fun _ : L1UnitBallIndex H => K) 1) (ε : ℝ) (_hε : 0 < ε) :
    Metric.ball (unitBallL1Quotient K H x) (ε / ‖c‖) ⊆
      unitBallL1Quotient K H '' Metric.ball x ε := by
  intro y hy
  obtain ⟨v, a, hqa, ha⟩ :=
    unitBallL1Quotient_exists_single_le c hc (y - unitBallL1Quotient K H x)
  have hy' : ‖y - unitBallL1Quotient K H x‖ < ε / ‖c‖ := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hy
  have hsmall : ‖lp.single (E := fun _ : L1UnitBallIndex H => K) 1 v a‖ < ε :=
    lt_of_le_of_lt ha
      (by simpa only [mul_comm] using (lt_div_iff₀ (zero_lt_one.trans hc)).mp hy')
  refine ⟨x + lp.single 1 v a, ?_, ?_⟩
  · simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left] using hsmall
  · rw [map_add, hqa, add_sub_cancel]

/-- Openness follows directly from the explicit ball inclusion. -/
theorem unitBallL1Quotient_isOpenMap : IsOpenMap (unitBallL1Quotient K H) := by
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm K
  intro U hU
  rw [Metric.isOpen_iff]
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x hx
  refine ⟨ε / ‖c‖, div_pos hε (zero_lt_one.trans hc), ?_⟩
  exact (unitBallL1Quotient_ball_subset c hc x ε hε).trans (Set.image_mono hball)

/-- The ordinary ℓ¹ closed-unit-ball quotient of a Banach space, with its sum formula,
coordinate values, contractive norm, single-coordinate lifts, and quantitative openness.
Completeness of the domain is supplied by the ordinary `lp` completeness instance. -/
theorem unitBall_l1_quotient [CompleteSpace K] (c : K) (hc : 1 < ‖c‖) :
    (∀ a, HasSum (fun v : L1UnitBallIndex H => a v • (v : H))
      (unitBallL1Quotient K H a)) ∧
    (∀ (v : L1UnitBallIndex H) (a : K),
      unitBallL1Quotient K H (lp.single 1 v a) = a • (v : H)) ∧
    ‖unitBallL1Quotient K H‖ ≤ 1 ∧
    (∀ h : H, ∃ v : L1UnitBallIndex H, ∃ a : K,
      unitBallL1Quotient K H (lp.single 1 v a) = h ∧
      ‖lp.single (E := fun _ : L1UnitBallIndex H => K) 1 v a‖ ≤ ‖c‖ * ‖h‖) ∧
    (∀ h : H, h ≠ 0 → ∃ v : L1UnitBallIndex H, ∃ a : K,
      unitBallL1Quotient K H (lp.single 1 v a) = h ∧
      ‖lp.single (E := fun _ : L1UnitBallIndex H => K) 1 v a‖ < ‖c‖ * ‖h‖) ∧
    Function.Surjective (unitBallL1Quotient K H) ∧
    IsOpenMap (unitBallL1Quotient K H) ∧
    (∀ x ε, 0 < ε → Metric.ball (unitBallL1Quotient K H x) (ε / ‖c‖) ⊆
      unitBallL1Quotient K H '' Metric.ball x ε) ∧
    CompleteSpace (lp (fun _ : L1UnitBallIndex H => K) 1) :=
  ⟨unitBallL1Quotient_hasSum, unitBallL1Quotient_single, norm_unitBallL1Quotient_le,
    unitBallL1Quotient_exists_single_le c hc, unitBallL1Quotient_exists_single_lt c hc,
    unitBallL1Quotient_surjective, unitBallL1Quotient_isOpenMap,
    unitBallL1Quotient_ball_subset c hc, inferInstance⟩

end AlternatingAnalytic
