/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
import AlternatingAnalytic.Analysis.CompletedBaseChange

/-!
# Base change of operators

For a bounded operator `f` on `V`, the map `f ⊗ id` on `V ⊗_K L` is `L`-linear, bounded by
`‖f‖`, and extends to the completed base change. The resulting map `f ↦ f_{K'}` is a
`K`-linear contraction (Lemma D.7).
-/

open scoped TensorProduct

namespace AlternatingAnalytic

/-- A normed algebra over a nontrivially normed field is nontrivially normed. -/
@[instance_reducible]
def normedExtensionNontriviallyNormedField (K L : Type*) [NontriviallyNormedField K]
    [NormedField L] [NormedAlgebra K L] : NontriviallyNormedField L where
  toNormedField := inferInstance
  non_trivial := by
    obtain ⟨c, hc⟩ := @NontriviallyNormedField.non_trivial K _
    exact ⟨algebraMap K L c, by simpa only [norm_algebraMap'] using hc⟩

universe u

variable (K : Type*) (V L : Type u) [NontriviallyNormedField K]
  [NormedAddCommGroup V] [NormedSpace K V] [NontriviallyNormedField L]
  [NormedAlgebra K L] [CompleteSpace K] [IsUltrametricDist K]
  [SphericallyCompleteSpace K] [IsUltrametricDist L]

attribute [local instance] baseChangeModule baseChangeNormedAddCommGroup
  baseChangeNormedSpaceRestrictScalars baseChangeNormedSpace baseChangeIsScalarTower

/-- The map `f ⊗ id` on `V ⊗[K] L`, as an `L`-linear map. -/
def baseChangeOperatorAlgebraic (f : V →L[K] V) : V ⊗[K] L →ₗ[L] V ⊗[K] L where
  toFun := f.toLinearMap.rTensor L
  map_add' := map_add _
  map_smul' a u := by
    change f.toLinearMap.rTensor L (a • u) = a • f.toLinearMap.rTensor L u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul v l => simp only [baseChange_smul_tmul, LinearMap.rTensor_tmul]
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]

omit [CompleteSpace K] [IsUltrametricDist K] [SphericallyCompleteSpace K]
  [IsUltrametricDist L] in
@[simp]
theorem baseChangeOperatorAlgebraic_tmul (f : V →L[K] V) (v : V) (l : L) :
    baseChangeOperatorAlgebraic K V L f (v ⊗ₜ[K] l) = f v ⊗ₜ[K] l := rfl

theorem norm_baseChangeOperatorAlgebraic_apply_le (f : V →L[K] V) (u : V ⊗[K] L) :
    ‖baseChangeOperatorAlgebraic K V L f u‖ ≤ ‖f‖ * ‖u‖ := by
  change ‖f.toLinearMap.rTensor L u‖ ≤ ‖f‖ * baseChangeSeminorm K V L u
  apply norm_le_baseChangeSeminorm _ (norm_nonneg f) ?_ u
  intro v l
  change baseChangeSeminorm K V L (f v ⊗ₜ[K] l) ≤ ‖f‖ * (‖v‖ * ‖l‖)
  calc
    _ ≤ ‖f v‖ * ‖l‖ := baseChangeSeminorm_tmul_le K V L (f v) l
    _ ≤ (‖f‖ * ‖v‖) * ‖l‖ :=
      mul_le_mul_of_nonneg_right (f.le_opNorm v) (norm_nonneg l)
    _ = ‖f‖ * (‖v‖ * ‖l‖) := mul_assoc _ _ _

/-- `f ⊗ id` as a bounded `L`-linear operator. -/
noncomputable def baseChangeOperatorContinuous (f : V →L[K] V) :
    V ⊗[K] L →L[L] V ⊗[K] L :=
  (baseChangeOperatorAlgebraic K V L f).mkContinuous ‖f‖
    (norm_baseChangeOperatorAlgebraic_apply_le K V L f)

/-- The extension of `f ⊗ id` to the completed base change. -/
noncomputable def completedBaseChangeOperator (f : V →L[K] V) :
    CompletedBaseChange K V L →L[L] CompletedBaseChange K V L :=
  (baseChangeOperatorContinuous K V L f).completion

@[simp]
theorem completedBaseChangeOperator_apply_tensor (f : V →L[K] V) (u : V ⊗[K] L) :
    completedBaseChangeOperator K V L f (baseChangeToCompletionK K V L u) =
      baseChangeToCompletionK K V L (baseChangeOperatorAlgebraic K V L f u) :=
  ContinuousLinearMap.completion_apply_coe _ _

theorem norm_completedBaseChangeOperator_apply_le (f : V →L[K] V)
    (x : CompletedBaseChange K V L) :
    ‖completedBaseChangeOperator K V L f x‖ ≤ ‖f‖ * ‖x‖ := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_le (completedBaseChangeOperator K V L f).continuous.norm
      (continuous_const.mul continuous_norm)
  | ih u =>
    change ‖completedBaseChangeOperator K V L f (baseChangeToCompletionK K V L u)‖ ≤
      ‖f‖ * ‖baseChangeToCompletionK K V L u‖
    rw [completedBaseChangeOperator_apply_tensor,
      (baseChangeToCompletionK K V L).norm_map, (baseChangeToCompletionK K V L).norm_map]
    exact norm_baseChangeOperatorAlgebraic_apply_le K V L f u

theorem norm_completedBaseChangeOperator_le (f : V →L[K] V) :
    ‖completedBaseChangeOperator K V L f‖ ≤ ‖f‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f)
    (norm_completedBaseChangeOperator_apply_le K V L f)

@[simp]
theorem completedBaseChangeOperator_embedding (f : V →L[K] V) (v : V) :
    completedBaseChangeOperator K V L f (completedBaseChangeEmbedding K V L v) =
      completedBaseChangeEmbedding K V L (f v) := by
  simp

/-- Operators on the completed base change are determined on the dense tensor subspace. -/
theorem completedBaseChangeOperator_ext
    {S T : CompletedBaseChange K V L →L[L] CompletedBaseChange K V L}
    (h : ∀ u : V ⊗[K] L,
      S (baseChangeToCompletionK K V L u) = T (baseChangeToCompletionK K V L u)) : S = T := by
  apply DFunLike.coe_injective
  exact (denseRange_baseChangeToCompletionK K V L).equalizer S.continuous T.continuous
    (funext h)

/-- Base change of operators is `K`-linear. -/
noncomputable def baseChangeOperatorsLinear :
    (V →L[K] V) →ₗ[K] (CompletedBaseChange K V L →L[L] CompletedBaseChange K V L) where
  toFun := completedBaseChangeOperator K V L
  map_add' f g := by
    apply completedBaseChangeOperator_ext K V L
    intro u
    simp [baseChangeOperatorAlgebraic]
  map_smul' c f := by
    apply completedBaseChangeOperator_ext K V L
    intro u
    simp [baseChangeOperatorAlgebraic]

/-- Base change of operators `f ↦ f_{K'}` as a `K`-linear contraction (Lemma D.7). -/
noncomputable def baseChangeOperators :
    (V →L[K] V) →L[K] (CompletedBaseChange K V L →L[L] CompletedBaseChange K V L) :=
  (baseChangeOperatorsLinear K V L).mkContinuous 1 fun f => by
    change ‖completedBaseChangeOperator K V L f‖ ≤ 1 * ‖f‖
    simpa only [one_mul] using norm_completedBaseChangeOperator_le K V L f

theorem norm_baseChangeOperators_le_one : ‖baseChangeOperators K V L‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

end AlternatingAnalytic
