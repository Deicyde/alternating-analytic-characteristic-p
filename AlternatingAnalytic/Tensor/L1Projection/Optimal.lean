/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
import AlternatingAnalytic.Tensor.L1Projection.Coordinates
import AlternatingAnalytic.Tensor.L1Projection.TestFamily
import AlternatingAnalytic.Analysis.L1PolynomialLift
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.Algebra.Order.Floor

/-!
# Optimal projections onto the diagonal of `T_n(ℓ¹)` (Proposition G.4)

Over a complete nonarchimedean field and for an infinite index set `I`, the smallest norm of a
projection `T_n(ℓ¹(I,K)) → Δ_n(ℓ¹(I,K))` is `n!`, so `ℓ¹(I,K)` does not have universal analytic
reflection.

The upper bound linearizes the sorted-orbit representative of the canonical tensor map from
`L1PolynomialLift.exists_l1_diagonal_lift`. For the lower bound, fix `n` distinct indices
`w`, put `x = ∑ e_{w j}` and expand `x^{⊗ n}` into basis tensors `e_{w ∘ ρ}`. The coordinate of
`R(x^{⊗ n}) = x^{⊗ n}` at `w` is `1`, so by the ultrametric inequality some `R(e_{w ∘ ρ})` has
coordinate of absolute value at least `1` at `w`, hence at all `n!` permutations of `w`; the
ℓ¹ coordinate bound then gives `‖R‖ ≥ n!`. The consequence uses the necessity half of
Theorem G.3 and the growth of `(n!)^{1/n}`.
-/

open Filter
open scoped TensorProduct BigOperators Topology Nat

namespace AlternatingAnalytic.L1Projection

universe uK uI

variable {K : Type uK} {I : Type uI} [NontriviallyNormedField K]

noncomputable local instance : DecidableEq I := Classical.decEq I

/-- The basis tensor `e_{w 0} ⊗ ⋯ ⊗ e_{w (n-1)}` in `T_n(ℓ¹(I,K))`. -/
noncomputable def basisTensor (n : ℕ) (w : Fin n → I) : TensorPower K (lp (fun _ : I => K) 1) n :=
  completedProjectiveTensorTprod (K := K) (fun _ : Fin n => lp (fun _ : I => K) 1)
    (fun r => lp.single 1 (w r) (1 : K))

theorem norm_basisTensor_le (n : ℕ) (w : Fin n → I) : ‖basisTensor (K := K) n w‖ ≤ 1 := by
  calc
    ‖basisTensor (K := K) n w‖ ≤
        ‖completedProjectiveTensorTprod (K := K) (fun _ : Fin n => lp (fun _ : I => K) 1)‖ *
          ∏ r, ‖lp.single (E := fun _ : I => K) 1 (w r) (1 : K)‖ :=
      ContinuousMultilinearMap.le_opNorm _ _
    _ ≤ 1 * 1 := by
      gcongr
      · exact norm_completedProjectiveTensorTprod_le _
      · exact (Finset.prod_eq_one fun r _ => by
          rw [lp.norm_single zero_lt_one, norm_one]).le
    _ = 1 := one_mul 1

/-- The sorted-orbit projection: a projection onto `Δ_n(ℓ¹(I,K))` of norm at most `n!`. -/
theorem exists_projection_norm_le_factorial (n : ℕ) :
    ∃ R : TensorPower K (lp (fun _ : I => K) 1) n →L[K]
        DiagonalSpan K (lp (fun _ : I => K) 1) n,
      (∀ t : DiagonalSpan K (lp (fun _ : I => K) 1) n,
        R (t : TensorPower K (lp (fun _ : I => K) 1) n) = t) ∧ ‖R‖ ≤ n ! := by
  obtain ⟨C, hC, hnorm⟩ := L1PolynomialLift.exists_l1_diagonal_lift
    (DiagonalSpan K (lp (fun _ : I => K) 1) n) (isClosed_diagonalSpan n) n
    (completedProjectiveTensorTprod (K := K) (fun _ : Fin n => lp (fun _ : I => K) 1))
    (fun x => diagonalTensor_mem n x)
  let R : TensorPower K (lp (fun _ : I => K) 1) n →L[K]
      DiagonalSpan K (lp (fun _ : I => K) 1) n :=
    completedProjectiveTensorLiftIsometry (fun _ : Fin n => lp (fun _ : I => K) 1)
      (DiagonalSpan K (lp (fun _ : I => K) 1) n) C
  have hR (x : lp (fun _ : I => K) 1) :
      (R (diagonalTensor K n x) : TensorPower K (lp (fun _ : I => K) 1) n) =
        diagonalTensor K n x :=
    (congrArg Subtype.val (completedProjectiveTensorLiftIsometry_tprod
      (fun _ : Fin n => lp (fun _ : I => K) 1) C (fun _ => x))).trans (hC x)
  refine ⟨R, fixes_of_fixes_diagonalTensor R hR, ?_⟩
  rw [show ‖R‖ = ‖C‖ from norm_completedProjectiveTensorLiftIsometry _ C]
  calc
    ‖C‖ ≤ n ! * ‖completedProjectiveTensorTprod (K := K)
        (fun _ : Fin n => lp (fun _ : I => K) 1)‖ := hnorm
    _ ≤ n ! * 1 := mul_le_mul_of_nonneg_left
      (norm_completedProjectiveTensorTprod_le _) (by positivity)
    _ = n ! := mul_one _

/-- Every projection onto `Δ_n(ℓ¹(I,K))` has norm at least `n!`, for nonarchimedean `K` and
infinite `I`. -/
theorem factorial_le_norm_of_projection [IsUltrametricDist K] [CompleteSpace K] [Infinite I]
    (n : ℕ)
    (R : TensorPower K (lp (fun _ : I => K) 1) n →L[K] DiagonalSpan K (lp (fun _ : I => K) 1) n)
    (hR : ∀ t : DiagonalSpan K (lp (fun _ : I => K) 1) n,
      R (t : TensorPower K (lp (fun _ : I => K) 1) n) = t) :
    (n ! : ℝ) ≤ ‖R‖ := by
  classical
  let w : Fin n → I := fun r => Infinite.natEmbedding I r
  have hw : Function.Injective w := (Infinite.natEmbedding I).injective.comp Fin.val_injective
  let x : lp (fun _ : I => K) 1 := ∑ j, lp.single 1 (w j) (1 : K)
  have hxw (r : Fin n) : x (w r) = 1 := by
    simp only [x, lp.coeFn_sum, Finset.sum_apply]
    rw [Finset.sum_eq_single r (fun j _ hj => lp.single_apply_ne 1 _ _ (hw.ne (Ne.symm hj)))
      (by simp), lp.single_apply_self]
  have hexp : diagonalTensor K n x = ∑ ρ : Fin n → Fin n, basisTensor (K := K) n (w ∘ ρ) := by
    rw [diagonalTensor_eq]
    exact (completedProjectiveTensorTprod (K := K) (fun _ : Fin n => lp (fun _ : I => K) 1)).map_sum
      (fun _ j => lp.single 1 (w j) (1 : K))
  have hfix : (R (diagonalTensor K n x) : TensorPower K (lp (fun _ : I => K) 1) n) =
      diagonalTensor K n x := congrArg Subtype.val (hR ⟨_, diagonalTensor_mem n x⟩)
  have hsum : ∑ ρ : Fin n → Fin n,
      coord n w (R (basisTensor (K := K) n (w ∘ ρ)) : TensorPower K (lp (fun _ : I => K) 1) n) =
        1 := by
    calc
      _ = coord n w (R (diagonalTensor K n x) : TensorPower K (lp (fun _ : I => K) 1) n) := by
        rw [hexp, map_sum, Submodule.coe_sum, map_sum]
      _ = 1 := by
        rw [hfix, coord_diagonalTensor]
        exact Finset.prod_eq_one fun r _ => hxw r
  obtain ⟨ρ, -, hρ⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
    (⟨id, Finset.mem_univ _⟩ : (Finset.univ : Finset (Fin n → Fin n)).Nonempty)
    (fun ρ => coord n w
      (R (basisTensor (K := K) n (w ∘ ρ)) : TensorPower K (lp (fun _ : I => K) 1) n))
  rw [hsum, norm_one] at hρ
  set τ : TensorPower K (lp (fun _ : I => K) 1) n :=
    (R (basisTensor (K := K) n (w ∘ ρ)) : TensorPower K (lp (fun _ : I => K) 1) n) with hτdef
  have hτ : τ ∈ DiagonalSpan K (lp (fun _ : I => K) 1) n := (R _).property
  have hinj : Function.Injective (fun σ : Equiv.Perm (Fin n) => w ∘ σ) :=
    fun σ σ' h => Equiv.ext fun r => hw (congrFun h r)
  have hlow := sum_norm_coord_le n hinj τ
  simp only [coord_comp_perm_of_mem w _ hτ, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul] at hlow
  calc
    (n ! : ℝ) = n ! * 1 := (mul_one _).symm
    _ ≤ n ! * ‖coord n w τ‖ := mul_le_mul_of_nonneg_left hρ (by positivity)
    _ ≤ ‖τ‖ := hlow
    _ ≤ ‖R‖ * ‖basisTensor (K := K) n (w ∘ ρ)‖ := R.le_opNorm _
    _ ≤ ‖R‖ * 1 := mul_le_mul_of_nonneg_left (norm_basisTensor_le n _) (norm_nonneg R)
    _ = ‖R‖ := mul_one _

/-- Proposition G.4, first part: the optimal norm of a projection onto
`Δ_n(ℓ¹(I,K))` is `n!`. -/
theorem sInf_norm_projection_eq_factorial [IsUltrametricDist K] [CompleteSpace K] [Infinite I]
    (n : ℕ) :
    sInf {c : ℝ | ∃ R : TensorPower K (lp (fun _ : I => K) 1) n →L[K]
        DiagonalSpan K (lp (fun _ : I => K) 1) n,
        (∀ t : DiagonalSpan K (lp (fun _ : I => K) 1) n,
          R (t : TensorPower K (lp (fun _ : I => K) 1) n) = t) ∧ ‖R‖ = c} =
      (n.factorial : ℝ) := by
  obtain ⟨R, hR, hle⟩ := exists_projection_norm_le_factorial (K := K) (I := I) n
  apply IsLeast.csInf_eq
  refine ⟨⟨R, hR, le_antisymm hle (factorial_le_norm_of_projection n R hR)⟩, ?_⟩
  rintro c ⟨R', hR', rfl⟩
  exact factorial_le_norm_of_projection n R' hR'

/-- Proposition G.4, second part: `ℓ¹(I,K)` does not have universal analytic
reflection. -/
theorem not_universalAnalyticReflection [IsUltrametricDist K] [CompleteSpace K] [Infinite I] :
    ¬ UniversalAnalyticReflection K (lp (fun _ : I => K) 1) := by
  intro h
  obtain ⟨R, hR, C, r, hC, hr, hbound⟩ := tensor_projections_of_universalAnalyticReflection h
  have key (m : ℕ) : ((m + 1) ! : ℝ) ≤ C * r ^ (m + 1) :=
    (factorial_le_norm_of_projection (m + 1) (R m) (hR m)).trans (hbound m)
  have hlim := FloorSemiring.tendsto_pow_div_factorial_atTop r
  obtain ⟨k, hk, hk1⟩ := ((hlim.eventually (gt_mem_nhds (inv_pos.mpr hC))).and
    (eventually_ge_atTop 1)).exists
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hfac : (0 : ℝ) < ((m + 1) ! : ℝ) := by positivity
  rw [div_lt_iff₀ hfac] at hk
  have := key m
  have h2 : C * r ^ (m + 1) < ((m + 1) ! : ℝ) := by
    calc
      C * r ^ (m + 1) < C * (C⁻¹ * ((m + 1) ! : ℝ)) := mul_lt_mul_of_pos_left hk hC
      _ = ((m + 1) ! : ℝ) := by field_simp
  linarith

end AlternatingAnalytic.L1Projection
