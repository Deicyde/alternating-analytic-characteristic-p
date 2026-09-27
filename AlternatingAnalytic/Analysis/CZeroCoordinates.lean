import AlternatingAnalytic.Analysis.CZeroArrayAlgebra
import AlternatingAnalytic.Analysis.CZeroArraySummability
import AlternatingAnalytic.Analysis.CZeroCoordinateBasics
import Mathlib.Data.Fintype.Pi
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Coordinate calculus and bounded coefficient arrays on discrete c₀

The parameter space is Mathlib's genuine supremum-norm `C₀(I, K)`. The scalar
field need not be complete. Only the value space of the bounded-array sum is
assumed complete.
-/

noncomputable section

open scoped Topology ZeroAtInfty BigOperators
open Filter

namespace CZero

variable {I K W : Type*} [TopologicalSpace I] [DiscreteTopology I]
  [NontriviallyNormedField K] [NormedAddCommGroup W] [NormedSpace K W] {n : ℕ}

omit [DiscreteTopology I] in
/-- On inputs supported in finite coordinate sets, the array sum is a finite sum. -/
theorem array_tsum_eq_sum (c : (Fin n → I) → W) (x : Fin n → C₀(I, K))
    (s : Fin n → Finset I) (hx : ∀ r i, i ∉ s r → x r i = 0) :
    (∑' a : Fin n → I, (∏ r, x r (a r)) • c a) =
      ∑ a ∈ Fintype.piFinset s, (∏ r, x r (a r)) • c a := by
  classical
  apply tsum_eq_sum
  intro a ha
  have ha' : ¬ ∀ r, a r ∈ s r := by
    simpa only [Fintype.mem_piFinset] using ha
  obtain ⟨r, hr⟩ := not_forall.mp ha'
  have hz : (∏ j, x j (a j)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ r) (hx r (a r) hr)
  rw [hz, zero_smul]

variable [IsUltrametricDist W] [CompleteSpace W]

/-- The unconditional bounded-array sum is multilinear. -/
def boundedArrayMultilinear (c : (Fin n → I) → W) (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ a, ‖c a‖ ≤ C) : MultilinearMap K (fun _ : Fin n => C₀(I, K)) W where
  toFun x := ∑' a, arraySummand c a x
  map_update_add' x r y z := by
    simp only [MultilinearMap.map_update_add]
    exact (summable_arraySummand c C hC hc (Function.update x r y)).tsum_add
      (summable_arraySummand c C hC hc (Function.update x r z))
  map_update_smul' x r b y := by
    simp only [MultilinearMap.map_update_smul]
    exact (summable_arraySummand c C hC hc (Function.update x r y)).tsum_const_smul b

@[simp]
theorem boundedArrayMultilinear_apply (c : (Fin n → I) → W) (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ a, ‖c a‖ ≤ C) (x : Fin n → C₀(I, K)) :
    boundedArrayMultilinear c C hC hc x = ∑' a, (∏ r, x r (a r)) • c a := rfl

/-- The nonarchimedean estimate gives the sharp product-norm bound. -/
theorem norm_boundedArrayMultilinear_apply_le (c : (Fin n → I) → W) (C : ℝ)
    (hC : 0 ≤ C) (hc : ∀ a, ‖c a‖ ≤ C) (x : Fin n → C₀(I, K)) :
    ‖boundedArrayMultilinear c C hC hc x‖ ≤ C * ∏ r, ‖x r‖ :=
  IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg
    (mul_nonneg hC (Finset.prod_nonneg (fun _ _ => norm_nonneg _)))
    (norm_arraySummand_le c C hC hc x)

/-- A bounded coefficient array defines a continuous multilinear map on discrete c₀.
Only the value space is required to be complete. -/
def boundedArrayMultilinearMap (c : (Fin n → I) → W) (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ a, ‖c a‖ ≤ C) : ContinuousMultilinearMap K (fun _ : Fin n => C₀(I, K)) W :=
  (boundedArrayMultilinear c C hC hc).mkContinuous C
    (norm_boundedArrayMultilinear_apply_le c C hC hc)

@[simp]
theorem boundedArrayMultilinearMap_apply (c : (Fin n → I) → W) (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ a, ‖c a‖ ≤ C) (x : Fin n → C₀(I, K)) :
    boundedArrayMultilinearMap c C hC hc x = ∑' a, (∏ r, x r (a r)) • c a := rfl

/-- The operator norm does not exceed the coefficient bound. -/
theorem norm_boundedArrayMultilinearMap_le (c : (Fin n → I) → W) (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ a, ‖c a‖ ≤ C) : ‖boundedArrayMultilinearMap (K := K) c C hC hc‖ ≤ C :=
  MultilinearMap.mkContinuous_norm_le _ hC _

/-- Compatibility of the actual continuous map with finite coordinate supports. -/
theorem boundedArrayMultilinearMap_finiteSupport (c : (Fin n → I) → W) (C : ℝ)
    (hC : 0 ≤ C) (hc : ∀ a, ‖c a‖ ≤ C) (x : Fin n → C₀(I, K))
    (s : Fin n → Finset I) (hx : ∀ r i, i ∉ s r → x r i = 0) :
    boundedArrayMultilinearMap c C hC hc x =
      ∑ a ∈ Fintype.piFinset s, (∏ r, x r (a r)) • c a :=
  array_tsum_eq_sum c x s hx

/-- Evaluation on coordinate-vector tuples recovers the coefficient array. -/
@[simp]
theorem boundedArrayMultilinearMap_coordinate (c : (Fin n → I) → W) (C : ℝ)
    (hC : 0 ≤ C) (hc : ∀ a, ‖c a‖ ≤ C) (a : Fin n → I) :
    boundedArrayMultilinearMap c C hC hc (fun r => coordinate (K := K) (a r)) = c a := by
  classical
  rw [boundedArrayMultilinearMap_apply, tsum_eq_single a]
  · simp
  · intro b hb
    obtain ⟨r, hr⟩ : ∃ r, b r ≠ a r := by
      by_contra h
      push Not at h
      exact hb (funext h)
    have hz : (∏ j, coordinate (K := K) (a j) (b j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ r) (by simp [hr])
    rw [hz, zero_smul]

/-- Applying the map to finite truncations gives the finite array polynomial. -/
theorem boundedArrayMultilinearMap_truncation (c : (Fin n → I) → W) (C : ℝ)
    (hC : 0 ≤ C) (hc : ∀ a, ‖c a‖ ≤ C) (x : Fin n → C₀(I, K))
    (s : Fin n → Finset I) :
    boundedArrayMultilinearMap c C hC hc (fun r => truncation (s r) (x r)) =
      ∑ a ∈ Fintype.piFinset s, (∏ r, x r (a r)) • c a := by
  classical
  rw [boundedArrayMultilinearMap_finiteSupport c C hC hc _ s
    (by intro r i hi; simp [hi])]
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  apply Finset.prod_congr rfl
  intro r _
  simp [(Fintype.mem_piFinset.mp ha) r]

/-- In degree zero the map is the constant given by the unique empty tuple. -/
@[simp]
theorem boundedArrayMultilinearMap_zero (c : (Fin 0 → I) → W) (C : ℝ)
    (hC : 0 ≤ C) (hc : ∀ a, ‖c a‖ ≤ C) (x : Fin 0 → C₀(I, K)) :
    boundedArrayMultilinearMap c C hC hc x = c Fin.elim0 := by
  have hx : x = fun r => coordinate (K := K) (Fin.elim0 r) := by
    funext r
    exact Fin.elim0 r
  rw [hx, boundedArrayMultilinearMap_coordinate]

/-- All guarantees of the bounded-array construction, in every degree and over
an arbitrary discrete index type: cofinite decay, unconditional summability, the
sum formula, the sharp operator-norm bound, recovery of the coefficients, and
compatibility with finite supports and finite truncations. -/
theorem boundedArrayMultilinearMap_spec (c : (Fin n → I) → W) (C : ℝ)
    (hC : 0 ≤ C) (hc : ∀ a, ‖c a‖ ≤ C) :
    let Q := boundedArrayMultilinearMap (K := K) c C hC hc
    (∀ x : Fin n → C₀(I, K),
      Tendsto (fun a => (∏ r, x r (a r)) • c a) cofinite (𝓝 0)) ∧
    (∀ x : Fin n → C₀(I, K), Summable (fun a => (∏ r, x r (a r)) • c a)) ∧
    (∀ x, Q x = ∑' a, (∏ r, x r (a r)) • c a) ∧
    ‖Q‖ ≤ C ∧
    (∀ x, ‖Q x‖ ≤ C * ∏ r, ‖x r‖) ∧
    (∀ a, Q (fun r => coordinate (K := K) (a r)) = c a) ∧
    (∀ (x : Fin n → C₀(I, K)) (s : Fin n → Finset I),
      (∀ r i, i ∉ s r → x r i = 0) →
      Q x = ∑ a ∈ Fintype.piFinset s, (∏ r, x r (a r)) • c a) ∧
    (∀ (x : Fin n → C₀(I, K)) (s : Fin n → Finset I),
      Q (fun r => truncation (s r) (x r)) =
        ∑ a ∈ Fintype.piFinset s, (∏ r, x r (a r)) • c a) := by
  exact ⟨tendsto_arraySummand_cofinite_zero c C hC hc,
    summable_arraySummand c C hC hc, boundedArrayMultilinearMap_apply c C hC hc,
    norm_boundedArrayMultilinearMap_le c C hC hc,
    norm_boundedArrayMultilinear_apply_le c C hC hc,
    boundedArrayMultilinearMap_coordinate c C hC hc,
    boundedArrayMultilinearMap_finiteSupport c C hC hc,
    boundedArrayMultilinearMap_truncation c C hC hc⟩

end CZero
