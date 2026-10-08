/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
import AlternatingAnalytic.Analysis.CompletedBaseChange
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Completed base change along the identity extension

When the extension field equals the base field, every algebraic tensor `u ∈ V ⊗_K K` is the
pure tensor `rid u ⊗ 1` (`x ⊗ λ = λx ⊗ 1`), so the dense inclusion into the completion has the
same range as the canonical isometry `ι_V`. For complete `V` this range is closed, hence
`ι_V : V → V ⊗̂_π K` is a surjective linear isometry. Consequently the completed base change
of an ultrametric Banach space (for instance `ℓ^∞(ℕ, K)`) is again ultrametric. This is
Remark E.2 of the paper (the case `K₁ = K̂`).
-/

open scoped TensorProduct BoundedContinuousFunction

namespace AlternatingAnalytic

universe u

section Self

variable (K V : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  [SphericallyCompleteSpace K] [NormedAddCommGroup V] [NormedSpace K V]

attribute [local instance] baseChangeModule baseChangeNormedAddCommGroup
  baseChangeNormedSpaceRestrictScalars baseChangeNormedSpace baseChangeIsScalarTower

omit [CompleteSpace K] [IsUltrametricDist K] [SphericallyCompleteSpace K] in
/-- Every tensor in `V ⊗_K K` is the pure tensor `rid u ⊗ 1`. -/
theorem rid_tmul_one_eq (u : V ⊗[K] K) : TensorProduct.rid K V u ⊗ₜ[K] (1 : K) = u := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul v a => rw [TensorProduct.rid_tmul, TensorProduct.smul_tmul,
      smul_eq_mul, mul_one]
  | add x y hx hy => rw [map_add, TensorProduct.add_tmul, hx, hy]

/-- Along the identity extension, `v ↦ v ⊗ 1` is surjective. -/
theorem baseChangeEmbedding_surjective_self :
    Function.Surjective (baseChangeEmbedding K V K) :=
  fun u => ⟨TensorProduct.rid K V u, rid_tmul_one_eq K V u⟩

/-- Along the identity extension, `ι_V` has dense range. -/
theorem denseRange_completedBaseChangeEmbedding_self :
    DenseRange (completedBaseChangeEmbedding K V K) := by
  have h : Set.range (completedBaseChangeEmbedding K V K) =
      Set.range (baseChangeToCompletionK K V K) := by
    change Set.range ((baseChangeToCompletionK K V K) ∘ (baseChangeEmbedding K V K)) = _
    exact (baseChangeEmbedding_surjective_self K V).range_comp _
  unfold DenseRange
  rw [h]
  exact denseRange_baseChangeToCompletionK K V K

/-- Along the identity extension, `ι_V` is surjective for complete `V`. -/
theorem completedBaseChangeEmbedding_surjective_self [CompleteSpace V] :
    Function.Surjective (completedBaseChangeEmbedding K V K) := by
  have hc : IsClosed (Set.range (completedBaseChangeEmbedding K V K)) :=
    ((completedBaseChangeEmbedding K V K).isometry.isUniformInducing.isComplete_range).isClosed
  rw [← Set.range_eq_univ, ← hc.closure_eq]
  exact (denseRange_completedBaseChangeEmbedding_self K V).closure_range

/-- Along the identity extension, `ι_V` is a linear isometric equivalence for complete `V`. -/
noncomputable def completedBaseChangeSelfEquiv [CompleteSpace V] :
    V ≃ₗᵢ[K] CompletedBaseChange K V K :=
  LinearIsometryEquiv.ofSurjective (completedBaseChangeEmbedding K V K)
    (completedBaseChangeEmbedding_surjective_self K V)

/-- Along the identity extension, the completed base change of a complete ultrametric space
is ultrametric. -/
theorem isUltrametricDist_completedBaseChange_self_of [CompleteSpace V] [IsUltrametricDist V] :
    IsUltrametricDist (CompletedBaseChange K V K) := by
  constructor
  intro x y z
  obtain ⟨a, rfl⟩ := completedBaseChangeEmbedding_surjective_self K V x
  obtain ⟨b, rfl⟩ := completedBaseChangeEmbedding_surjective_self K V y
  obtain ⟨c, rfl⟩ := completedBaseChangeEmbedding_surjective_self K V z
  simp only [(completedBaseChangeEmbedding K V K).isometry.dist_eq]
  exact IsUltrametricDist.dist_triangle_max a b c

end Self

/-- Bounded continuous functions into an ultrametric space carry the ultrametric sup distance. -/
theorem BoundedContinuousFunction.isUltrametricDist {α β : Type*} [TopologicalSpace α]
    [PseudoMetricSpace β] [IsUltrametricDist β] : IsUltrametricDist (α →ᵇ β) := by
  constructor
  intro f g h
  apply (BoundedContinuousFunction.dist_le (by positivity)).2
  intro s
  exact (IsUltrametricDist.dist_triangle_max (f s) (g s) (h s)).trans
    (max_le_max (BoundedContinuousFunction.dist_coe_le_dist s)
      (BoundedContinuousFunction.dist_coe_le_dist s))

/-- Along the identity extension, `ℓ^∞(ℕ, K) ⊗̂_π K` is ultrametric. -/
theorem isUltrametricDist_completedBaseChange_boundedSeq_self
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    [SphericallyCompleteSpace K] :
    IsUltrametricDist (CompletedBaseChange K (ℕ →ᵇ K) K) :=
  haveI : IsUltrametricDist (ℕ →ᵇ K) := BoundedContinuousFunction.isUltrametricDist
  isUltrametricDist_completedBaseChange_self_of K (ℕ →ᵇ K)

end AlternatingAnalytic
