/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
import Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSeminorm
import Mathlib.Analysis.Normed.Module.Completion

/-!
# Completed ordinary projective tensors

The Hausdorff completion of Mathlib's ordinary projective seminorm represents continuous
multilinear maps into complete normed spaces, preserving the operator norm. The projective
seminorm uses sums of products of norms. No separation of the algebraic tensor is assumed.
-/

open scoped TensorProduct

namespace AlternatingAnalytic

section Completion

variable {K V Z : Type*} [NontriviallyNormedField K]
  [SeminormedAddCommGroup V] [NormedSpace K V]
  [NormedAddCommGroup Z] [NormedSpace K Z] [CompleteSpace Z]

private theorem norm_fromCompletion (f : V →L[K] Z) : ‖f.fromCompletion‖ = ‖f‖ := by
  apply le_antisymm
  · apply f.fromCompletion.opNorm_le_bound (norm_nonneg f)
    intro x
    induction x using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih x =>
      simpa only [ContinuousLinearMap.fromCompletion_apply_coe,
        UniformSpace.Completion.norm_coe] using f.le_opNorm x
  · apply f.opNorm_le_bound (norm_nonneg f.fromCompletion)
    intro x
    simpa only [ContinuousLinearMap.fromCompletion_apply_coe,
      UniformSpace.Completion.norm_coe] using
      f.fromCompletion.le_opNorm (x : UniformSpace.Completion V)

private noncomputable def completionLiftIsometry :
    (V →L[K] Z) ≃ₗᵢ[K] (UniformSpace.Completion V →L[K] Z) where
  toFun := ContinuousLinearMap.fromCompletion
  invFun := fun f => f.comp UniformSpace.Completion.toComplL
  left_inv f := by
    ext x
    simp
  right_inv f := by
    apply ContinuousLinearMap.fromCompletion_unique
    intro x
    rfl
  map_add' f g := by
    apply ContinuousLinearMap.fromCompletion_unique
    intro x
    simp
  map_smul' c f := by
    apply ContinuousLinearMap.fromCompletion_unique
    intro x
    simp
  norm_map' := norm_fromCompletion

end Completion

variable (K : Type*) [NontriviallyNormedField K]
  {ι : Type*} [Fintype ι] (E : ι → Type*)
  [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace K (E i)]

/-- The separated completion of the ordinary projective tensor seminorm. -/
abbrev CompletedProjectiveTensor := UniformSpace.Completion (⨂[K] i, E i)

/-- The ordinary completed projective tensor power, including the zeroth power. -/
abbrev CompletedProjectiveTensorPower (P : Type*) [SeminormedAddCommGroup P]
    [NormedSpace K P] (n : ℕ) :=
  CompletedProjectiveTensor K (fun _ : Fin n => P)

variable {K}

/-- The canonical multilinear map followed by the Hausdorff completion map. -/
noncomputable def completedProjectiveTensorTprod :
    ContinuousMultilinearMap K E (CompletedProjectiveTensor K E) :=
  UniformSpace.Completion.toComplL.compContinuousMultilinearMap (PiTensorProduct.tprodL K)

@[simp]
theorem completedProjectiveTensorTprod_apply (x : ∀ i, E i) :
    completedProjectiveTensorTprod (K := K) E x =
      ((⨂ₜ[K] i, x i) : CompletedProjectiveTensor K E) := rfl

theorem norm_completedProjectiveTensorTprod_le :
    ‖completedProjectiveTensorTprod (K := K) E‖ ≤ 1 := by
  refine ContinuousMultilinearMap.opNorm_le_bound zero_le_one fun x => ?_
  simpa only [completedProjectiveTensorTprod_apply, UniformSpace.Completion.norm_coe, one_mul]
    using PiTensorProduct.projectiveSeminorm_tprod_le (𝕜 := K) x

/-- All pure tensors have dense linear span in the separated completion. -/
theorem completedProjectiveTensor_tprod_dense_span :
    (Submodule.span K
      (Set.range (completedProjectiveTensorTprod (K := K) E))).topologicalClosure = ⊤ := by
  let S := Submodule.span K (Set.range (completedProjectiveTensorTprod (K := K) E))
  apply Submodule.eq_top_iff'.mpr
  intro t
  refine UniformSpace.Completion.induction_on t isClosed_closure ?_
  intro a
  induction a using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [UniformSpace.Completion.coe_smul]
    apply S.topologicalClosure.smul_mem
    apply S.le_topologicalClosure
    exact Submodule.subset_span ⟨x, rfl⟩
  | add a b ha hb =>
    rw [UniformSpace.Completion.coe_add]
    exact S.topologicalClosure.add_mem ha hb

variable (Z : Type*) [NormedAddCommGroup Z] [NormedSpace K Z] [CompleteSpace Z]

/-- The isometric universal linearization into a complete normed target. Its forward map
extends the algebraic projective tensor lift to the Hausdorff completion. -/
noncomputable def completedProjectiveTensorLiftIsometry :
    ContinuousMultilinearMap K E Z ≃ₗᵢ[K] (CompletedProjectiveTensor K E →L[K] Z) :=
  (PiTensorProduct.liftIsometry K E Z).trans completionLiftIsometry

@[simp]
theorem completedProjectiveTensorLiftIsometry_apply (B : ContinuousMultilinearMap K E Z) :
    completedProjectiveTensorLiftIsometry E Z B =
      (PiTensorProduct.liftIsometry K E Z B).fromCompletion := rfl

@[simp]
theorem completedProjectiveTensorLiftIsometry_symm_apply
    (L : CompletedProjectiveTensor K E →L[K] Z) :
    (completedProjectiveTensorLiftIsometry E Z).symm L =
      L.compContinuousMultilinearMap (completedProjectiveTensorTprod E) := rfl

variable {Z}

@[simp]
theorem completedProjectiveTensorLiftIsometry_tprod
    (B : ContinuousMultilinearMap K E Z) (x : ∀ i, E i) :
    completedProjectiveTensorLiftIsometry E Z B
      (completedProjectiveTensorTprod E x) = B x := by
  simp

@[simp]
theorem completedProjectiveTensorLiftIsometry_comp_tprod
    (B : ContinuousMultilinearMap K E Z) :
    (completedProjectiveTensorLiftIsometry E Z B).compContinuousMultilinearMap
      (completedProjectiveTensorTprod E) = B := by
  ext x
  exact completedProjectiveTensorLiftIsometry_tprod E B x

@[simp]
theorem norm_completedProjectiveTensorLiftIsometry (B : ContinuousMultilinearMap K E Z) :
    ‖completedProjectiveTensorLiftIsometry E Z B‖ = ‖B‖ :=
  (completedProjectiveTensorLiftIsometry E Z).norm_map B

theorem completedProjectiveTensorLift_unique (B : ContinuousMultilinearMap K E Z)
    (L : CompletedProjectiveTensor K E →L[K] Z)
    (hL : L.compContinuousMultilinearMap (completedProjectiveTensorTprod E) = B) :
    L = completedProjectiveTensorLiftIsometry E Z B := by
  apply (completedProjectiveTensorLiftIsometry (K := K) E Z).symm.injective
  simpa only [LinearIsometryEquiv.symm_apply_apply,
    completedProjectiveTensorLiftIsometry_symm_apply] using hL

variable (Z)

/-- The completed ordinary projective tensor universal property: the canonical map is
contractive and its pure tensors span densely; every continuous multilinear map into the
given Banach target has a unique continuous linear lift with exactly the same norm. -/
theorem completedProjectiveTensor_universal :
    ‖completedProjectiveTensorTprod (K := K) E‖ ≤ 1 ∧
    (Submodule.span K
      (Set.range (completedProjectiveTensorTprod (K := K) E))).topologicalClosure = ⊤ ∧
    ∀ B : ContinuousMultilinearMap K E Z,
      (completedProjectiveTensorLiftIsometry E Z B).compContinuousMultilinearMap
        (completedProjectiveTensorTprod E) = B ∧
      (∀ x : ∀ i, E i, completedProjectiveTensorLiftIsometry E Z B
        (completedProjectiveTensorTprod E x) = B x) ∧
      ‖completedProjectiveTensorLiftIsometry E Z B‖ = ‖B‖ ∧
      ∀ L : CompletedProjectiveTensor K E →L[K] Z,
        L.compContinuousMultilinearMap (completedProjectiveTensorTprod E) = B →
          L = completedProjectiveTensorLiftIsometry E Z B := by
  refine ⟨norm_completedProjectiveTensorTprod_le E,
    completedProjectiveTensor_tprod_dense_span E, fun B => ?_⟩
  exact ⟨completedProjectiveTensorLiftIsometry_comp_tprod E B,
    completedProjectiveTensorLiftIsometry_tprod E B,
    norm_completedProjectiveTensorLiftIsometry E B,
    fun L hL => completedProjectiveTensorLift_unique E B L hL⟩

end AlternatingAnalytic
