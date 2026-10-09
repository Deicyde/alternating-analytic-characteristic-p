/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
import AlternatingAnalytic.Analysis.ProjectiveBaseChange
import AlternatingAnalytic.Analysis.ScalarProjection
import Mathlib.Analysis.Normed.Module.Completion

/-!
# Completed projective scalar extension

For a spherically complete field `K` and an extension `L`, the map `v ↦ v ⊗ 1`
from `V` into `V ⊗[K] L` with the projective norm is isometric. The completion of
`V ⊗[K] L` is a Banach space over `L`, and a complete `V` is a `K`-linear retract
of it with a retraction of norm at most one. These are parts (3) and (4) of
Lemma D.6.
-/

open scoped TensorProduct

namespace AlternatingAnalytic

universe u

variable (K : Type*) (V L : Type u) [NontriviallyNormedField K]
  [NormedAddCommGroup V] [NormedSpace K V] [NormedField L] [NormedAlgebra K L]
  [CompleteSpace K] [IsUltrametricDist K] [SphericallyCompleteSpace K]
  [IsUltrametricDist L]

attribute [local instance] baseChangeModule baseChangeNormedAddCommGroup
  baseChangeNormedSpaceRestrictScalars baseChangeNormedSpace baseChangeIsScalarTower

omit [CompleteSpace K] in
/-- Scalar inclusion preserves the ordinary projective norm. -/
theorem baseChangeSeminorm_tmul_one (v : V) :
    baseChangeSeminorm K V L (v ⊗ₜ[K] (1 : L)) = ‖v‖ := by
  refine le_antisymm ?_ ?_
  · simpa only [norm_one, mul_one] using baseChangeSeminorm_tmul_le K V L v (1 : L)
  · obtain ⟨π, hπ, hfix⟩ := exists_scalar_projection K L
    have hone : π (1 : L) = 1 := by simpa using hfix 1
    have h := norm_scalarContraction_le π (v ⊗ₜ[K] (1 : L))
    simp only [scalarContraction_tmul, ContinuousLinearMap.coe_coe, hone, one_smul] at h
    exact h.trans ((mul_le_mul_of_nonneg_right hπ (apply_nonneg _ _)).trans_eq (one_mul _))

/-- The map `v ↦ v ⊗ 1` as a `K`-linear isometry. -/
noncomputable def baseChangeEmbedding : V →ₗᵢ[K] V ⊗[K] L where
  toLinearMap := (TensorProduct.mk K V L).flip 1
  norm_map' := baseChangeSeminorm_tmul_one K V L

@[simp]
theorem baseChangeEmbedding_apply (v : V) :
    baseChangeEmbedding K V L v = v ⊗ₜ[K] (1 : L) := rfl

/-- The completion of `V ⊗[K] L` with the projective norm. -/
def CompletedBaseChange := UniformSpace.Completion (V ⊗[K] L)

noncomputable instance completedBaseChangeNormedAddCommGroup :
    NormedAddCommGroup (CompletedBaseChange K V L) :=
  inferInstanceAs (NormedAddCommGroup (UniformSpace.Completion (V ⊗[K] L)))

noncomputable instance completedBaseChangeNormedSpace :
    NormedSpace L (CompletedBaseChange K V L) :=
  inferInstanceAs (NormedSpace L (UniformSpace.Completion (V ⊗[K] L)))

noncomputable instance completedBaseChangeNormedSpaceRestrictScalars :
    NormedSpace K (CompletedBaseChange K V L) :=
  inferInstanceAs (NormedSpace K (UniformSpace.Completion (V ⊗[K] L)))

instance completedBaseChangeCompleteSpace : CompleteSpace (CompletedBaseChange K V L) :=
  inferInstanceAs (CompleteSpace (UniformSpace.Completion (V ⊗[K] L)))

instance completedBaseChangeIsScalarTower : IsScalarTower K L (CompletedBaseChange K V L) :=
  inferInstanceAs (IsScalarTower K L (UniformSpace.Completion (V ⊗[K] L)))

/-- The dense inclusion of `V ⊗[K] L` into its completion, as an `L`-linear isometry. -/
noncomputable def baseChangeToCompletion : V ⊗[K] L →ₗᵢ[L] CompletedBaseChange K V L :=
  UniformSpace.Completion.toComplₗᵢ

/-- The same inclusion as a `K`-linear isometry. -/
noncomputable def baseChangeToCompletionK : V ⊗[K] L →ₗᵢ[K] CompletedBaseChange K V L :=
  UniformSpace.Completion.toComplₗᵢ

theorem denseRange_baseChangeToCompletion : DenseRange (baseChangeToCompletion K V L) :=
  UniformSpace.Completion.denseRange_coe

theorem denseRange_baseChangeToCompletionK : DenseRange (baseChangeToCompletionK K V L) :=
  UniformSpace.Completion.denseRange_coe

/-- The isometric embedding of `V` into the completed scalar extension. -/
noncomputable def completedBaseChangeEmbedding : V →ₗᵢ[K] CompletedBaseChange K V L :=
  (baseChangeToCompletionK K V L).comp (baseChangeEmbedding K V L)

@[simp]
theorem completedBaseChangeEmbedding_apply (v : V) :
    completedBaseChangeEmbedding K V L v =
      baseChangeToCompletionK K V L (v ⊗ₜ[K] (1 : L)) := rfl

/-- A bounded `K`-linear functional on `L` induces a bounded map `V ⊗[K] L → V`. -/
noncomputable def scalarContractionContinuous (ψ : L →L[K] K) : V ⊗[K] L →L[K] V :=
  (scalarContraction ψ.toLinearMap).mkContinuous ‖ψ‖ (norm_scalarContraction_le ψ)

@[simp]
theorem scalarContractionContinuous_apply (ψ : L →L[K] K) (u : V ⊗[K] L) :
    scalarContractionContinuous K V L ψ u = scalarContraction ψ.toLinearMap u := rfl

variable [CompleteSpace V]

/-- The extension of a scalar contraction to the completed tensor product. -/
noncomputable def completedScalarContraction (ψ : L →L[K] K) :
    CompletedBaseChange K V L →L[K] V :=
  (scalarContractionContinuous K V L ψ).fromCompletion

@[simp]
theorem completedScalarContraction_apply_tensor (ψ : L →L[K] K) (u : V ⊗[K] L) :
    completedScalarContraction K V L ψ (baseChangeToCompletionK K V L u) =
      scalarContraction ψ.toLinearMap u :=
  ContinuousLinearMap.fromCompletion_apply_coe _ _

theorem norm_completedScalarContraction_apply_le (ψ : L →L[K] K)
    (x : CompletedBaseChange K V L) :
    ‖completedScalarContraction K V L ψ x‖ ≤ ‖ψ‖ * ‖x‖ := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_le (completedScalarContraction K V L ψ).continuous.norm
      (continuous_const.mul continuous_norm)
  | ih u =>
    change ‖completedScalarContraction K V L ψ (baseChangeToCompletionK K V L u)‖ ≤
      ‖ψ‖ * ‖baseChangeToCompletionK K V L u‖
    rw [completedScalarContraction_apply_tensor, (baseChangeToCompletionK K V L).norm_map]
    exact norm_scalarContraction_le ψ u

theorem norm_completedScalarContraction_le (ψ : L →L[K] K) :
    ‖completedScalarContraction K V L ψ‖ ≤ ‖ψ‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg ψ)
    (norm_completedScalarContraction_apply_le K V L ψ)

/-- A complete `V` is a retract of its completed scalar extension, with a retraction
of norm at most one. -/
theorem exists_completedBaseChange_retraction :
    ∃ P : CompletedBaseChange K V L →L[K] V,
      ‖P‖ ≤ 1 ∧ ∀ v : V, P (completedBaseChangeEmbedding K V L v) = v := by
  obtain ⟨π, hπ, hfix⟩ := exists_scalar_projection K L
  refine ⟨completedScalarContraction K V L π,
    (norm_completedScalarContraction_le K V L π).trans hπ, ?_⟩
  intro v
  have hone : π (1 : L) = 1 := by simpa using hfix 1
  simp [hone]

end AlternatingAnalytic
