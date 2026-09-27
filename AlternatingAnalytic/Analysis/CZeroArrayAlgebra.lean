import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.Normed.Module.Multilinear.Basic

/-!
# Multilinear coordinate summands on spaces of functions vanishing at infinity

These algebraic summands and their supremum-norm estimates do not require completeness.
-/

open scoped BigOperators ZeroAtInfty

namespace CZero

variable {I K W : Type*} [TopologicalSpace I] [NontriviallyNormedField K]
  [NormedAddCommGroup W] [NormedSpace K W] {n : ℕ}

private def coordinateLinearMap (i : I) : C₀(I, K) →ₗ[K] K where
  toFun x := x i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The multilinear summand belonging to one coefficient of an array. -/
noncomputable def arraySummand (c : (Fin n → I) → W) (a : Fin n → I) :
    MultilinearMap K (fun _ : Fin n => C₀(I, K)) W :=
  ((MultilinearMap.mkPiAlgebra K (Fin n) K).compLinearMap
    (fun r => coordinateLinearMap (a r))).smulRight (c a)

@[simp]
theorem arraySummand_apply (c : (Fin n → I) → W) (a : Fin n → I)
    (x : Fin n → C₀(I, K)) :
    arraySummand c a x = (∏ r, x r (a r)) • c a :=
  rfl

/-- A bounded coefficient gives the product of the input supremum norms as a bound. -/
theorem norm_arraySummand_le (c : (Fin n → I) → W) (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ a, ‖c a‖ ≤ C) (x : Fin n → C₀(I, K)) (a : Fin n → I) :
    ‖arraySummand c a x‖ ≤ C * ∏ r, ‖x r‖ := by
  rw [arraySummand_apply, norm_smul, norm_prod, mul_comm]
  apply mul_le_mul (hc a)
  · exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      (fun r _ => (x r).toBCF.norm_coe_le_norm (a r))
  · exact Finset.prod_nonneg (fun _ _ => norm_nonneg _)
  · exact hC

end CZero
