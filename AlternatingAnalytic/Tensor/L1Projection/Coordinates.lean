/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
import AlternatingAnalytic.Tensor.L1Projection.Basic
import AlternatingAnalytic.Analysis.L1ProductSummation
import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Coordinates on the tensor powers of ordinary ℓ¹

For a tuple `v : Fin n → I`, the coordinate functional `coord n v` on `T_n(ℓ¹(I,K))` sends a pure
tensor `x₁ ⊗ ⋯ ⊗ xₙ` to `∏ r, x_r (v r)`. These functionals are contractive, and for any finite
family of distinct tuples their absolute values sum to at most the tensor norm, because the
coordinate array of a pure tensor is a product of `ℓ¹` arrays. Every element of the diagonal
span `Δ_n` has the same coordinate at all permutations of a tuple. These are the facts about
`T_n(ℓ¹(I,K)) = ℓ¹(Iⁿ,K)` used in the lower bound of Proposition G.4.
-/

open scoped TensorProduct BigOperators

namespace AlternatingAnalytic.L1Projection

universe uK uI

variable {K : Type uK} {I : Type uI} [NontriviallyNormedField K]

/-- The coordinate monomial `x ↦ ∏ r, x r (v r)` on `ℓ¹(I,K)ⁿ`. -/
noncomputable def coordMultilinear (n : ℕ) (v : Fin n → I) :
    MultilinearMap K (fun _ : Fin n => lp (fun _ : I => K) 1) K :=
  (MultilinearMap.mkPiAlgebra K (Fin n) K).compLinearMap
    (fun r => lp.evalₗ (fun _ : I => K) 1 (v r))

@[simp]
theorem coordMultilinear_apply (n : ℕ) (v : Fin n → I)
    (x : Fin n → lp (fun _ : I => K) 1) :
    coordMultilinear (K := K) n v x = ∏ r, x r (v r) := rfl

theorem norm_coordMultilinear_le (n : ℕ) (v : Fin n → I)
    (x : Fin n → lp (fun _ : I => K) 1) :
    ‖coordMultilinear (K := K) n v x‖ ≤ 1 * ∏ r, ‖x r‖ := by
  rw [coordMultilinear_apply, norm_prod, one_mul]
  exact Finset.prod_le_prod₀ (fun r _ => norm_nonneg _)
    (fun r _ => lp.norm_apply_le_norm one_ne_zero (x r) (v r))

/-- The coordinate monomial as a contractive continuous multilinear map. -/
noncomputable def coordContinuousMultilinear (n : ℕ) (v : Fin n → I) :
    ContinuousMultilinearMap K (fun _ : Fin n => lp (fun _ : I => K) 1) K :=
  (coordMultilinear n v).mkContinuous 1 (norm_coordMultilinear_le n v)

/-- The coordinates at a finite family of tuples, valued in finite-dimensional `ℓ¹`. -/
noncomputable def familyMultilinear (n : ℕ) {α : Type*} [Fintype α] (u : α → Fin n → I) :
    MultilinearMap K (fun _ : Fin n => lp (fun _ : I => K) 1) (PiLp 1 (fun _ : α => K)) :=
  (WithLp.linearEquiv 1 K (α → K)).symm.toLinearMap.compMultilinearMap
    (MultilinearMap.pi fun a => coordMultilinear n (u a))

theorem familyMultilinear_apply (n : ℕ) {α : Type*} [Fintype α] (u : α → Fin n → I)
    (x : Fin n → lp (fun _ : I => K) 1) (a : α) :
    familyMultilinear (K := K) n u x a = ∏ r, x r (u a r) := rfl

/-- For distinct tuples, the coordinate array of a pure tensor has ℓ¹ norm at most the product
of the norms. -/
theorem sum_prod_norm_le (n : ℕ) {α : Type*} [Fintype α] {u : α → Fin n → I}
    (hu : Function.Injective u) (x : Fin n → lp (fun _ : I => K) 1) :
    ∑ a : α, ∏ r, ‖x r (u a r)‖ ≤ ∏ r, ‖x r‖ := by
  classical
  calc
    ∑ a : α, ∏ r, ‖x r (u a r)‖ = ∑ v ∈ Finset.univ.image u, ∏ r, ‖x r (v r)‖ := by
      rw [Finset.sum_image (fun a _ b _ h => hu h)]
    _ ≤ ∏ r, ‖x r‖ := sum_le_hasSum _
      (fun v _ => Finset.prod_nonneg fun r _ => norm_nonneg _)
      (L1Coordinates.hasSum_prod_norm n x)

/-- The finite coordinate array as a contractive continuous multilinear map. -/
noncomputable def familyContinuousMultilinear (n : ℕ) {α : Type*} [Fintype α]
    {u : α → Fin n → I} (hu : Function.Injective u) :
    ContinuousMultilinearMap K (fun _ : Fin n => lp (fun _ : I => K) 1)
      (PiLp 1 (fun _ : α => K)) :=
  (familyMultilinear n u).mkContinuous 1 (fun x => by
    rw [PiLp.norm_eq_of_L1, one_mul]
    simpa only [familyMultilinear_apply, norm_prod] using sum_prod_norm_le n hu x)

theorem norm_familyContinuousMultilinear_le (n : ℕ) {α : Type*} [Fintype α]
    {u : α → Fin n → I} (hu : Function.Injective u) :
    ‖familyContinuousMultilinear (K := K) n hu‖ ≤ 1 :=
  MultilinearMap.mkContinuous_norm_le _ zero_le_one _

variable [CompleteSpace K]

/-- The coordinate functional at a tuple `v` on `T_n(ℓ¹(I,K))`. -/
noncomputable def coord (n : ℕ) (v : Fin n → I) :
    TensorPower K (lp (fun _ : I => K) 1) n →L[K] K :=
  completedProjectiveTensorLiftIsometry (fun _ : Fin n => lp (fun _ : I => K) 1) K
    (coordContinuousMultilinear n v)

theorem coord_tprod (n : ℕ) (v : Fin n → I) (x : Fin n → lp (fun _ : I => K) 1) :
    coord n v (completedProjectiveTensorTprod (K := K) (fun _ : Fin n => lp (fun _ : I => K) 1)
      x) = ∏ r, x r (v r) := by
  rw [coord, completedProjectiveTensorLiftIsometry_tprod]
  rfl

theorem coord_diagonalTensor (n : ℕ) (v : Fin n → I) (x : lp (fun _ : I => K) 1) :
    coord n v (diagonalTensor K n x) = ∏ r, x (v r) :=
  coord_tprod n v (fun _ => x)

/-- The finite coordinate array on `T_n(ℓ¹(I,K))`. -/
noncomputable def familyCoord (n : ℕ) {α : Type*} [Fintype α] {u : α → Fin n → I}
    (hu : Function.Injective u) :
    TensorPower K (lp (fun _ : I => K) 1) n →L[K] PiLp 1 (fun _ : α => K) :=
  completedProjectiveTensorLiftIsometry (fun _ : Fin n => lp (fun _ : I => K) 1) _
    (familyContinuousMultilinear (K := K) n hu)

theorem familyCoord_apply (n : ℕ) {α : Type*} [Fintype α] {u : α → Fin n → I}
    (hu : Function.Injective u) (t : TensorPower K (lp (fun _ : I => K) 1) n) (a : α) :
    familyCoord n hu t a = coord n (u a) t := by
  have h : (PiLp.proj 1 (fun _ : α => K) a).comp (familyCoord n hu) = coord n (u a) := by
    apply completedProjectiveTensorLift_unique
    ext x
    simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
      ContinuousLinearMap.comp_apply, familyCoord, completedProjectiveTensorLiftIsometry_tprod]
    rfl
  exact congrArg (fun L => L t) h

/-- For distinct tuples, the coordinates of a tensor have absolute sum at most its norm. -/
theorem sum_norm_coord_le (n : ℕ) {α : Type*} [Fintype α] {u : α → Fin n → I}
    (hu : Function.Injective u) (t : TensorPower K (lp (fun _ : I => K) 1) n) :
    ∑ a, ‖coord n (u a) t‖ ≤ ‖t‖ := by
  have hnorm : ‖familyCoord (K := K) n hu‖ ≤ 1 := by
    rw [familyCoord, norm_completedProjectiveTensorLiftIsometry]
    exact norm_familyContinuousMultilinear_le n hu
  calc
    ∑ a, ‖coord n (u a) t‖ = ‖familyCoord n hu t‖ := by
      rw [PiLp.norm_eq_of_L1]
      simp only [familyCoord_apply]
    _ ≤ ‖familyCoord (K := K) n hu‖ * ‖t‖ := (familyCoord n hu).le_opNorm t
    _ ≤ 1 * ‖t‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg t)
    _ = ‖t‖ := one_mul _

/-- Elements of the diagonal span have equal coordinates at permuted tuples. -/
theorem coord_comp_perm_of_mem {n : ℕ} (v : Fin n → I) (σ : Equiv.Perm (Fin n))
    {t : TensorPower K (lp (fun _ : I => K) 1) n}
    (ht : t ∈ DiagonalSpan K (lp (fun _ : I => K) 1) n) :
    coord n (v ∘ σ) t = coord n v t := by
  let L : TensorPower K (lp (fun _ : I => K) 1) n →L[K] K := coord n (v ∘ σ) - coord n v
  have hle := diagonalSpan_le
    (LinearMap.ker (L : TensorPower K (lp (fun _ : I => K) 1) n →ₗ[K] K))
    (ContinuousLinearMap.isClosed_ker _) (fun x => by
      rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, sub_apply,
        coord_diagonalTensor, coord_diagonalTensor, sub_eq_zero]
      exact Equiv.prod_comp σ (fun r => x (v r)))
  have := hle ht
  rwa [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, sub_apply,
    sub_eq_zero] at this

end AlternatingAnalytic.L1Projection
