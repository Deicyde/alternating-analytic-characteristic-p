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

The canonical map into algebraic scalar extension is isometric. Its completion is a
Banach space over the extension field, and a complete original space is a contracting
linear retract over the original field. This is `sources/charp.tex`, lemma `bc` (3)–(4).
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

/-- The actual map `v ↦ v ⊗ 1` as a linear isometry over the original field. -/
noncomputable def baseChangeEmbedding : V →ₗᵢ[K] V ⊗[K] L where
  toLinearMap := (TensorProduct.mk K V L).flip 1
  norm_map' := baseChangeSeminorm_tmul_one K V L

@[simp]
theorem baseChangeEmbedding_apply (v : V) :
    baseChangeEmbedding K V L v = v ⊗ₜ[K] (1 : L) := rfl

/-- The actual uniform completion of the projectively normed algebraic tensor product. -/
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

/-- The dense algebraic tensor inclusion, linear and isometric over the extension field. -/
noncomputable def baseChangeToCompletion : V ⊗[K] L →ₗᵢ[L] CompletedBaseChange K V L :=
  UniformSpace.Completion.toComplₗᵢ

/-- The same dense inclusion with its original-field linear structure. -/
noncomputable def baseChangeToCompletionK : V ⊗[K] L →ₗᵢ[K] CompletedBaseChange K V L :=
  UniformSpace.Completion.toComplₗᵢ

theorem denseRange_baseChangeToCompletion : DenseRange (baseChangeToCompletion K V L) :=
  UniformSpace.Completion.denseRange_coe

theorem denseRange_baseChangeToCompletionK : DenseRange (baseChangeToCompletionK K V L) :=
  UniformSpace.Completion.denseRange_coe

/-- The canonical isometric embedding of the original space into completed scalar extension. -/
noncomputable def completedBaseChangeEmbedding : V →ₗᵢ[K] CompletedBaseChange K V L :=
  (baseChangeToCompletionK K V L).comp (baseChangeEmbedding K V L)

@[simp]
theorem completedBaseChangeEmbedding_apply (v : V) :
    completedBaseChangeEmbedding K V L v =
      baseChangeToCompletionK K V L (v ⊗ₜ[K] (1 : L)) := rfl

/-- A scalar functional induces a bounded linear map on algebraic scalar extension. -/
noncomputable def scalarContractionContinuous (ψ : L →L[K] K) : V ⊗[K] L →L[K] V :=
  (scalarContraction ψ.toLinearMap).mkContinuous ‖ψ‖ (norm_scalarContraction_le ψ)

@[simp]
theorem scalarContractionContinuous_apply (ψ : L →L[K] K) (u : V ⊗[K] L) :
    scalarContractionContinuous K V L ψ u = scalarContraction ψ.toLinearMap u := rfl

variable [CompleteSpace V]

/-- Extension of a scalar contraction to the actual completed tensor product. -/
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

/-- A complete original space is a norm-one retract of its completed scalar extension. -/
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
