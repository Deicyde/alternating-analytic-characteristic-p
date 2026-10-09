/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
import AlternatingAnalytic.Analysis.CompletedBaseChange
import AlternatingAnalytic.Analysis.BaseChangeAlternatingCriterion
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

/-!
# Base change of alternating forms

Defines the base change `m ↦ m_{K'}` of bounded alternating maps to the completed
base change and shows it is a contraction (Lemma D.8). Bounded linear maps are extended first;
multilinear maps are then extended one variable at a time by currying.
-/

open scoped TensorProduct

namespace AlternatingAnalytic

universe u

section LinearExtension

variable (K : Type*) (E L : Type u) [NontriviallyNormedField K]
  [NormedAddCommGroup E] [NormedSpace K E] [NontriviallyNormedField L]
  [NormedAlgebra K L] [CompleteSpace K] [IsUltrametricDist K]
  [SphericallyCompleteSpace K] [IsUltrametricDist L]
  (G : Type*) [NormedAddCommGroup G] [NormedSpace K G] [NormedSpace L G]
  [IsScalarTower K L G] [CompleteSpace G]

attribute [local instance] baseChangeModule baseChangeNormedAddCommGroup
  baseChangeNormedSpaceRestrictScalars baseChangeNormedSpace baseChangeIsScalarTower

/-- The map `x ⊗ l ↦ l • f x` on the algebraic tensor product. -/
def scalarExtensionTensorMap (f : E →L[K] G) : E ⊗[K] L →ₗ[K] G :=
  TensorProduct.lift (LinearMap.mk₂ K (fun x l => l • f x)
    (by intros; simp [map_add, smul_add])
    (by intro c x l; simp only [map_smul]; exact smul_comm l c (f x))
    (by intros; simp [add_smul])
    (by intros; simp [smul_assoc]))

omit [CompleteSpace K] [IsUltrametricDist K] [SphericallyCompleteSpace K]
  [IsUltrametricDist L] [CompleteSpace G] in
@[simp]
theorem scalarExtensionTensorMap_tmul (f : E →L[K] G) (x : E) (l : L) :
    scalarExtensionTensorMap K E L G f (x ⊗ₜ[K] l) = l • f x := rfl

/-- `scalarExtensionTensorMap` as an `L`-linear map. -/
def scalarExtensionTensorMapL (f : E →L[K] G) : E ⊗[K] L →ₗ[L] G where
  toFun := scalarExtensionTensorMap K E L G f
  map_add' := map_add _
  map_smul' a u := by
    change scalarExtensionTensorMap K E L G f (a • u) =
      a • scalarExtensionTensorMap K E L G f u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul x l => simp [mul_smul]
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]

omit [CompleteSpace G] in
theorem norm_scalarExtensionTensorMap_le (f : E →L[K] G) (u : E ⊗[K] L) :
    ‖scalarExtensionTensorMap K E L G f u‖ ≤ ‖f‖ * ‖u‖ := by
  apply norm_le_baseChangeSeminorm _ (norm_nonneg f) ?_ u
  intro x l
  rw [scalarExtensionTensorMap_tmul, norm_smul]
  calc
    ‖l‖ * ‖f x‖ ≤ ‖l‖ * (‖f‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left (f.le_opNorm x) (norm_nonneg l)
    _ = ‖f‖ * (‖x‖ * ‖l‖) := by ring

/-- Bounded scalar extension before completion. -/
noncomputable def scalarExtensionTensorContinuous (f : E →L[K] G) : E ⊗[K] L →L[L] G :=
  (scalarExtensionTensorMapL K E L G f).mkContinuous ‖f‖
    (norm_scalarExtensionTensorMap_le K E L G f)

/-- Base change of a bounded linear map into a complete `L`-space. -/
noncomputable def scalarExtensionLinear (f : E →L[K] G) :
    CompletedBaseChange K E L →L[L] G :=
  (scalarExtensionTensorContinuous K E L G f).fromCompletion

@[simp]
theorem scalarExtensionLinear_apply_tensor (f : E →L[K] G) (u : E ⊗[K] L) :
    scalarExtensionLinear K E L G f (baseChangeToCompletionK K E L u) =
      scalarExtensionTensorMap K E L G f u :=
  ContinuousLinearMap.fromCompletion_apply_coe _ _

@[simp]
theorem scalarExtensionLinear_embedding (f : E →L[K] G) (x : E) :
    scalarExtensionLinear K E L G f (completedBaseChangeEmbedding K E L x) = f x := by
  simp

theorem norm_scalarExtensionLinear_apply_le (f : E →L[K] G)
    (x : CompletedBaseChange K E L) :
    ‖scalarExtensionLinear K E L G f x‖ ≤ ‖f‖ * ‖x‖ := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_le (scalarExtensionLinear K E L G f).continuous.norm
      (continuous_const.mul continuous_norm)
  | ih u =>
    change ‖scalarExtensionLinear K E L G f (baseChangeToCompletionK K E L u)‖ ≤
      ‖f‖ * ‖baseChangeToCompletionK K E L u‖
    rw [scalarExtensionLinear_apply_tensor, (baseChangeToCompletionK K E L).norm_map]
    exact norm_scalarExtensionTensorMap_le K E L G f u

theorem norm_scalarExtensionLinear_le (f : E →L[K] G) :
    ‖scalarExtensionLinear K E L G f‖ ≤ ‖f‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f)
    (norm_scalarExtensionLinear_apply_le K E L G f)

/-- `scalarExtensionLinear` is linear in the original map. -/
noncomputable def scalarExtensionLinearFamily :
    (E →L[K] G) →ₗ[K] (CompletedBaseChange K E L →L[L] G) where
  toFun := scalarExtensionLinear K E L G
  map_add' f g := by
    apply DFunLike.coe_injective
    apply (denseRange_baseChangeToCompletionK K E L).equalizer
      (scalarExtensionLinear K E L G (f + g)).continuous
      (scalarExtensionLinear K E L G f + scalarExtensionLinear K E L G g).continuous
    funext u
    simp only [Function.comp_apply, scalarExtensionLinear_apply_tensor,
      add_apply]
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul x l => simp [smul_add]
    | add x y hx hy => simp only [map_add, hx, hy]; abel
  map_smul' c f := by
    apply DFunLike.coe_injective
    apply (denseRange_baseChangeToCompletionK K E L).equalizer
      (scalarExtensionLinear K E L G (c • f)).continuous
      (c • scalarExtensionLinear K E L G f).continuous
    funext u
    simp only [Function.comp_apply, scalarExtensionLinear_apply_tensor,
      smul_apply]
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul x l =>
      simp only [scalarExtensionTensorMap_tmul, smul_apply]
      exact smul_comm l c (f x)
    | add x y hx hy => simp only [map_add, hx, hy, smul_add]

/-- `scalarExtensionLinear` as a contraction. -/
noncomputable def scalarExtensionLinearFamilyContinuous :
    (E →L[K] G) →L[K] (CompletedBaseChange K E L →L[L] G) :=
  (scalarExtensionLinearFamily K E L G).mkContinuous 1 fun f => by
    change ‖scalarExtensionLinear K E L G f‖ ≤ 1 * ‖f‖
    simpa only [one_mul] using norm_scalarExtensionLinear_le K E L G f

/-- Base change of multilinear maps in zero variables. -/
noncomputable def scalarExtensionMultilinearZero :
    (E [×0]→L[K] G) →L[K] (CompletedBaseChange K E L [×0]→L[L] G) :=
  LinearMap.mkContinuous
    { toFun := fun m => ContinuousMultilinearMap.uncurry0 L (CompletedBaseChange K E L) (m 0)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun m => by simp)

/-- Extend the first variable after extending all remaining variables. -/
noncomputable def scalarExtensionMultilinearStep {n : ℕ}
    (T : (E [×n]→L[K] G) →L[K] (CompletedBaseChange K E L [×n]→L[L] G)) :
    (E [×(n + 1)]→L[K] G) →L[K] (CompletedBaseChange K E L [×(n + 1)]→L[L] G) :=
  ((continuousMultilinearCurryLeftEquiv L
      (fun _ : Fin (n + 1) => CompletedBaseChange K E L) G).symm.toLinearIsometry.toContinuousLinearMap.restrictScalars K).comp
    ((scalarExtensionLinearFamilyContinuous K E L
        (CompletedBaseChange K E L [×n]→L[L] G)).comp
      ((ContinuousLinearMap.compL K E (E [×n]→L[K] G)
          (CompletedBaseChange K E L [×n]→L[L] G) T).comp
        (continuousMultilinearCurryLeftEquiv K (fun _ : Fin (n + 1) => E) G).toLinearIsometry.toContinuousLinearMap))

@[simp]
theorem scalarExtensionMultilinearStep_apply {n : ℕ}
    (T : (E [×n]→L[K] G) →L[K] (CompletedBaseChange K E L [×n]→L[L] G))
    (m : E [×(n + 1)]→L[K] G) :
    scalarExtensionMultilinearStep K E L G T m =
      (scalarExtensionLinear K E L (CompletedBaseChange K E L [×n]→L[L] G)
        (T.comp m.curryLeft)).uncurryLeft := rfl

theorem norm_scalarExtensionMultilinearStep_apply_le {n : ℕ}
    (T : (E [×n]→L[K] G) →L[K] (CompletedBaseChange K E L [×n]→L[L] G))
    (hT : ∀ m, ‖T m‖ ≤ ‖m‖) (m : E [×(n + 1)]→L[K] G) :
    ‖scalarExtensionMultilinearStep K E L G T m‖ ≤ ‖m‖ := by
  rw [scalarExtensionMultilinearStep_apply, ContinuousLinearMap.uncurryLeft_norm]
  apply (norm_scalarExtensionLinear_le K E L _ _).trans
  calc
    ‖T.comp m.curryLeft‖ ≤ ‖T‖ * ‖m.curryLeft‖ := T.opNorm_comp_le _
    _ ≤ 1 * ‖m.curryLeft‖ := mul_le_mul_of_nonneg_right
      (ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by simpa using hT))
      (norm_nonneg m.curryLeft)
    _ = ‖m‖ := by simp

/-- Base change of continuous multilinear maps by iterated currying. -/
noncomputable def scalarExtensionMultilinear : (n : ℕ) →
    (E [×n]→L[K] G) →L[K] (CompletedBaseChange K E L [×n]→L[L] G)
  | 0 => scalarExtensionMultilinearZero K E L G
  | n + 1 => scalarExtensionMultilinearStep K E L G
      (scalarExtensionMultilinear n)

theorem norm_scalarExtensionMultilinear_apply_le (n : ℕ) (m : E [×n]→L[K] G) :
    ‖scalarExtensionMultilinear K E L G n m‖ ≤ ‖m‖ := by
  induction n with
  | zero =>
    change ‖ContinuousMultilinearMap.uncurry0 L (CompletedBaseChange K E L) (m 0)‖ ≤ ‖m‖
    simp
  | succ n ih => exact norm_scalarExtensionMultilinearStep_apply_le K E L G _ ih m

@[simp]
theorem scalarExtensionMultilinear_embedding (n : ℕ) (m : E [×n]→L[K] G)
    (x : Fin n → E) :
    scalarExtensionMultilinear K E L G n m
      (fun i => completedBaseChangeEmbedding K E L (x i)) = m x := by
  induction n with
  | zero =>
    change m 0 = m x
    congr 1
    exact Subsingleton.elim _ _
  | succ n ih =>
    change scalarExtensionLinear K E L (CompletedBaseChange K E L [×n]→L[L] G)
      ((scalarExtensionMultilinear K E L G n).comp m.curryLeft)
      (completedBaseChangeEmbedding K E L (x 0))
      (fun i => completedBaseChangeEmbedding K E L (x i.succ)) = m x
    rw [scalarExtensionLinear_embedding]
    change scalarExtensionMultilinear K E L G n (m.curryLeft (x 0))
      (fun i => completedBaseChangeEmbedding K E L (x i.succ)) = m x
    rw [ih]
    exact congrArg m (Fin.cons_self_tail x)

/-- Base change of an alternating map into a complete `L`-space. -/
noncomputable def scalarExtensionAlternating (n : ℕ) (m : E [⋀^Fin n]→L[K] G) :
    CompletedBaseChange K E L [⋀^Fin n]→L[L] G where
  toContinuousMultilinearMap :=
    scalarExtensionMultilinear K E L G n m.toContinuousMultilinearMap
  map_eq_zero_of_eq' := alternating_of_baseChangeEmbedding K E L
    (scalarExtensionMultilinear K E L G n m.toContinuousMultilinearMap) m
    (scalarExtensionMultilinear_embedding K E L G n m.toContinuousMultilinearMap)

@[simp]
theorem scalarExtensionAlternating_embedding (n : ℕ) (m : E [⋀^Fin n]→L[K] G)
    (x : Fin n → E) :
    scalarExtensionAlternating K E L G n m
      (fun i => completedBaseChangeEmbedding K E L (x i)) = m x :=
  scalarExtensionMultilinear_embedding K E L G n m.toContinuousMultilinearMap x

theorem norm_scalarExtensionAlternating_le (n : ℕ) (m : E [⋀^Fin n]→L[K] G) :
    ‖scalarExtensionAlternating K E L G n m‖ ≤ ‖m‖ :=
  norm_scalarExtensionMultilinear_apply_le K E L G n m.toContinuousMultilinearMap

/-- `scalarExtensionAlternating` is linear in the form. -/
noncomputable def scalarExtensionAlternatingLinear (n : ℕ) :
    (E [⋀^Fin n]→L[K] G) →ₗ[K] (CompletedBaseChange K E L [⋀^Fin n]→L[L] G) where
  toFun := scalarExtensionAlternating K E L G n
  map_add' f g := by
    apply ContinuousAlternatingMap.toContinuousMultilinearMap_injective
    change scalarExtensionMultilinear K E L G n
      (f.toContinuousMultilinearMap + g.toContinuousMultilinearMap) = _
    exact map_add _ _ _
  map_smul' c f := by
    apply ContinuousAlternatingMap.toContinuousMultilinearMap_injective
    change scalarExtensionMultilinear K E L G n (c • f.toContinuousMultilinearMap) = _
    exact map_smul _ _ _

/-- `scalarExtensionAlternating` as a contraction. -/
noncomputable def scalarExtensionAlternatingFamily (n : ℕ) :
    (E [⋀^Fin n]→L[K] G) →L[K] (CompletedBaseChange K E L [⋀^Fin n]→L[L] G) :=
  (scalarExtensionAlternatingLinear K E L G n).mkContinuous 1 fun m => by
    change ‖scalarExtensionAlternating K E L G n m‖ ≤ 1 * ‖m‖
    simpa only [one_mul] using norm_scalarExtensionAlternating_le K E L G n m

end LinearExtension

section Forms

variable (K : Type*) (E F L : Type u) [NontriviallyNormedField K]
  [NormedAddCommGroup E] [NormedSpace K E] [NormedAddCommGroup F] [NormedSpace K F]
  [NontriviallyNormedField L] [NormedAlgebra K L] [CompleteSpace K]
  [IsUltrametricDist K] [SphericallyCompleteSpace K] [IsUltrametricDist L]

/-- The base change `m ↦ m_{K'}` of alternating forms (Lemma D.8), as a `K`-linear map. -/
noncomputable def baseChangeAlternatingForms (n : ℕ) :
    (E [⋀^Fin n]→L[K] F) →L[K]
      (CompletedBaseChange K E L [⋀^Fin n]→L[L] CompletedBaseChange K F L) :=
  (scalarExtensionAlternatingFamily K E L (CompletedBaseChange K F L) n).comp
    (ContinuousLinearMap.compContinuousAlternatingMapCLM K E F
      (CompletedBaseChange K F L) (Fin n)
      (completedBaseChangeEmbedding K F L).toContinuousLinearMap)

theorem norm_baseChangeAlternatingForms_apply_le (n : ℕ) (m : E [⋀^Fin n]→L[K] F) :
    ‖baseChangeAlternatingForms K E F L n m‖ ≤ ‖m‖ := by
  change ‖scalarExtensionAlternating K E L (CompletedBaseChange K F L) n
    ((completedBaseChangeEmbedding K F L).toContinuousLinearMap.compContinuousAlternatingMap m)‖ ≤ ‖m‖
  calc
    _ ≤ ‖(completedBaseChangeEmbedding K F L).toContinuousLinearMap.compContinuousAlternatingMap m‖ :=
      norm_scalarExtensionAlternating_le K E L (CompletedBaseChange K F L) n _
    _ = ‖m‖ := (completedBaseChangeEmbedding K F L).norm_compContinuousAlternatingMap m

theorem norm_baseChangeAlternatingForms_le (n : ℕ) :
    ‖baseChangeAlternatingForms K E F L n‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun m => by
    simpa only [one_mul] using norm_baseChangeAlternatingForms_apply_le K E F L n m

@[simp]
theorem baseChangeAlternatingForms_embedding (n : ℕ) (m : E [⋀^Fin n]→L[K] F)
    (x : Fin n → E) :
    baseChangeAlternatingForms K E F L n m
      (fun i => completedBaseChangeEmbedding K E L (x i)) =
      completedBaseChangeEmbedding K F L (m x) :=
  scalarExtensionAlternating_embedding K E L (CompletedBaseChange K F L) n
    ((completedBaseChangeEmbedding K F L).toContinuousLinearMap.compContinuousAlternatingMap m) x

end Forms

end AlternatingAnalytic
