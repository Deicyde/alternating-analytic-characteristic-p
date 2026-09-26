import AlternatingAnalytic.Analysis.DeterminantCoefficientSpaces
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# The actual padded carriers and their concrete completions

The original carriers retain their inherited maximum norms over the incomplete
rational field. The complete models have their explicit Laurent-field vector
space structures. Every completion identification preserves the original dense
isometric inclusion.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NNReal

namespace AlternatingAnalytic.DeterminantPair.Padding

variable (p : ℕ) [Fact p.Prime] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] (n : ℕ)
attribute [local instance] DeterminantPair.preferredNormedFieldK
  DeterminantPair.preferredFieldK DeterminantPair.preferredFieldL

/-- The padded source remains finite-dimensional algebraically over K. -/
theorem finiteDimensional_E : FiniteDimensional (K p r) (E p r n) := inferInstance

/-- The padded determinant carrier remains finite-dimensional algebraically over K. -/
theorem finiteDimensional_D : FiniteDimensional (K p r) (D p r n) := inferInstance

theorem finrank_E : Module.finrank (K p r) (E p r n) = p + 1 + n := by
  change Module.finrank (K p r)
    (RigidDenseSource.Concrete.source p r × (Fin n → K p r)) = _
  rw [Module.finrank_prod, RigidDenseSource.Concrete.finrank_source, Module.finrank_pi]
  simp

/-- The complete ambient product has its literal L-module and normed-space structures. -/
abbrev ambientNormedSpace : NormedSpace (L p r) (H p r n) := inferInstance

instance finiteDimensional_H : FiniteDimensional (L p r) (H p r n) :=
  (basis p r n).finiteDimensional_of_finite

theorem ambient_model : CompleteSpace (H p r n) ∧ FiniteDimensional (L p r) (H p r n) ∧
    Module.finrank (L p r) (H p r n) = p + n := by
  exact ⟨inferInstance, inferInstance, finrank_paddedAmbient p r n⟩

private theorem ultrametric_pi {I F : Type*} [Fintype I] [NormedAddCommGroup F]
    [IsUltrametricDist F] : IsUltrametricDist (I → F) := by
  apply IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
  intro x y
  apply (pi_norm_le_iff_of_nonneg (le_trans (norm_nonneg x) (le_max_left _ _))).2
  intro i
  exact (IsUltrametricDist.norm_add_le_max (x i) (y i)).trans
    (max_le_max (norm_le_pi_norm x i) (norm_le_pi_norm y i))

private theorem ultrametric_prod {F J : Type*} [NormedAddCommGroup F]
    [NormedAddCommGroup J] [IsUltrametricDist F] [IsUltrametricDist J] :
    IsUltrametricDist (F × J) := by
  apply IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
  intro x y
  change max ‖x.1 + y.1‖ ‖x.2 + y.2‖ ≤ max (max ‖x.1‖ ‖x.2‖) (max ‖y.1‖ ‖y.2‖)
  exact max_le
    ((IsUltrametricDist.norm_add_le_max x.1 y.1).trans
      (max_le_max (le_max_left _ _) (le_max_left _ _)))
    ((IsUltrametricDist.norm_add_le_max x.2 y.2).trans
      (max_le_max (le_max_right _ _) (le_max_right _ _)))

instance isUltrametric_auxiliaryK : IsUltrametricDist (Fin n → K p r) := ultrametric_pi
instance isUltrametric_auxiliaryL : IsUltrametricDist (Fin n → L p r) := ultrametric_pi
instance isUltrametric_E : IsUltrametricDist (E p r n) := ultrametric_prod
instance isUltrametric_D : IsUltrametricDist (D p r n) := ultrametric_prod
instance isUltrametric_H : IsUltrametricDist (H p r n) := ultrametric_prod

/-- The coefficient space is dense: it contains 1, hence the dense rational field. -/
theorem denseRange_inclusionC : DenseRange (C p r).subtypeₗᵢ :=
  denseRange_subtype_of_one (C p r)
    (RationalField.denseRange_algebraMap (ZMod p) r) (one_mem_C p r)

/-- The rational scalar field is actually contained in the coefficient space. -/
theorem algebraMap_mem_C (a : K p r) : algebraMap (K p r) (L p r) a ∈ C p r := by
  simpa only [Algebra.smul_def, mul_one] using (C p r).smul_mem a (one_mem_C p r)

/-- Completion of the padded rigid source is its concrete ambient product. -/
def completionE : UniformSpace.Completion (E p r n) ≃ₗᵢ[K p r] H p r n :=
  LinearIsometryEquiv.ofSurjective (inclusionE p r n).fromCompletion (by
    intro x
    exact (denseRange_inclusionE p r n).induction_on x
      (inclusionE p r n).fromCompletion.isometry.isClosedEmbedding.isClosed_range
      (fun e => ⟨e, (inclusionE p r n).fromCompletion_apply_coe e⟩))

/-- Completion of the padded determinant source is the same ambient product. -/
def completionD : UniformSpace.Completion (D p r n) ≃ₗᵢ[K p r] H p r n :=
  LinearIsometryEquiv.ofSurjective (inclusionD p r n).fromCompletion (by
    intro x
    exact (denseRange_inclusionD p r n).induction_on x
      (inclusionD p r n).fromCompletion.isometry.isClosedEmbedding.isClosed_range
      (fun d => ⟨d, (inclusionD p r n).fromCompletion_apply_coe d⟩))

/-- Completion of the actual small coefficient target is the Laurent field. -/
def completionC : UniformSpace.Completion (C p r) ≃ₗᵢ[K p r] L p r :=
  denseSubmoduleCompletionEquiv (C p r) (denseRange_inclusionC p r)

@[simp] theorem completionE_apply_coe (x : E p r n) :
    completionE p r n (x : UniformSpace.Completion (E p r n)) = inclusionE p r n x :=
  (inclusionE p r n).fromCompletion_apply_coe x

@[simp] theorem completionD_apply_coe (x : D p r n) :
    completionD p r n (x : UniformSpace.Completion (D p r n)) = inclusionD p r n x :=
  (inclusionD p r n).fromCompletion_apply_coe x

@[simp] theorem completionC_apply_coe (x : C p r) :
    completionC p r (x : UniformSpace.Completion (C p r)) = (x : L p r) :=
  denseSubmoduleCompletionEquiv_apply_coe _ _ x

/-- The original examples have finite algebraic dimension and the stated
inherited/max ultrametric norms; no completeness of K or G is asserted. -/
theorem finite_ultrametric_carriers :
    FiniteDimensional (K p r) (E p r n) ∧
    FiniteDimensional (K p r) (D p r n) ∧
    FiniteDimensional (K p r) (G p r) ∧
    Module.finrank (K p r) (E p r n) = p + 1 + n ∧
    IsUltrametricDist (E p r n) ∧ IsUltrametricDist (D p r n) ∧
    IsUltrametricDist (G p r) ∧
    (∀ x : E p r n, ‖x‖ = max ‖x.1‖ ‖x.2‖) ∧
    (∀ x : D p r n, ‖x‖ = max ‖x.1‖ ‖x.2‖) ∧
    (∀ x : G p r, ‖x‖ = ‖(x : L p r)‖) :=
  ⟨finiteDimensional_E p r n, finiteDimensional_D p r n, inferInstance,
    finrank_E p r n, inferInstance, inferInstance, inferInstance,
    norm_E p r n, norm_D p r n, DeterminantPair.norm_G p r⟩

/-- All concrete completion identifications needed for `dom:limits`, with the
original inclusions and explicit complete finite-dimensional L-space model. -/
theorem concrete_completions :
    Isometry (inclusionE p r n) ∧ DenseRange (inclusionE p r n) ∧
    Isometry (inclusionD p r n) ∧ DenseRange (inclusionD p r n) ∧
    Isometry (G p r).subtypeₗᵢ ∧ DenseRange (G p r).subtypeₗᵢ ∧
    Isometry (C p r).subtypeₗᵢ ∧ DenseRange (C p r).subtypeₗᵢ ∧
    (∀ a : K p r, algebraMap (K p r) (L p r) a ∈ C p r) ∧
    (∀ x : E p r n,
      completionE p r n (x : UniformSpace.Completion (E p r n)) = inclusionE p r n x) ∧
    (∀ x : D p r n,
      completionD p r n (x : UniformSpace.Completion (D p r n)) = inclusionD p r n x) ∧
    (∀ x : G p r,
      DeterminantPair.completionG p r (x : UniformSpace.Completion (G p r)) = (x : L p r)) ∧
    (∀ x : C p r,
      completionC p r (x : UniformSpace.Completion (C p r)) = (x : L p r)) ∧
    CompleteSpace (H p r n) ∧ FiniteDimensional (L p r) (H p r n) ∧
    Module.finrank (L p r) (H p r n) = p + n ∧
    (∀ (a : L p r) (x : H p r n), ‖a • x‖ = ‖a‖ * ‖x‖) ∧
    CompleteSpace (L p r) := by
  exact ⟨(inclusionE p r n).isometry, denseRange_inclusionE p r n,
    (inclusionD p r n).isometry, denseRange_inclusionD p r n,
    (G p r).subtypeₗᵢ.isometry, denseRange_G_subtype p r,
    (C p r).subtypeₗᵢ.isometry, denseRange_inclusionC p r, algebraMap_mem_C p r,
    completionE_apply_coe p r n, completionD_apply_coe p r n,
    DeterminantPair.completionG_apply_coe p r, completionC_apply_coe p r,
    inferInstance, inferInstance, finrank_paddedAmbient p r n, norm_smul, inferInstance⟩

end AlternatingAnalytic.DeterminantPair.Padding
