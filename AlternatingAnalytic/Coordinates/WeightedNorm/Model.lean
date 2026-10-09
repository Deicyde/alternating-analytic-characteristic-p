/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
import AlternatingAnalytic.Coordinates.WeightedNorm.Basic

/-!
# Normed models of the weighted norm

A model of `(C₀(ℕ, β), ‖·‖_w)` is a normed space `G` with a linear isomorphism
`e : G ≃ₗ C₀(ℕ, β)` such that `‖g‖ = ‖e g‖_w` for all `g`. The norm of a model is between the
supremum norm and `3/2` times it, and a model is ultrametric, resp. complete, when `β` is.
-/

set_option backward.isDefEq.respectTransparency false

open scoped ZeroAtInfty

namespace AlternatingAnalytic.WeightedNorm

variable {𝕜 β G : Type*} [NormedField 𝕜] [NormedAddCommGroup β] [NormedSpace 𝕜 β]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] (e : G ≃ₗ[𝕜] C₀(ℕ, β))

/-- In a model, `‖e g‖_∞ ≤ ‖g‖ ≤ (3/2)‖e g‖_∞`. -/
theorem model_norm_bounds (he : ∀ g, ‖g‖ = wNorm (e g)) (g : G) :
    ‖e g‖ ≤ ‖g‖ ∧ ‖g‖ ≤ 3 / 2 * ‖e g‖ := by
  rw [he g]
  exact ⟨norm_le_wNorm _, wNorm_le _⟩

/-- A model is ultrametric when `β` is. -/
theorem model_norm_add_le_max [IsUltrametricDist β] (he : ∀ g, ‖g‖ = wNorm (e g)) (x y : G) :
    ‖x + y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [he, he, he, map_add]
  exact wNorm_add_le_max _ _

theorem model_isUltrametricDist [IsUltrametricDist β] (he : ∀ g, ‖g‖ = wNorm (e g)) :
    IsUltrametricDist G :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
    (model_norm_add_le_max e he)

/-- The linear isomorphism of a model is a continuous linear equivalence. -/
noncomputable def modelContinuousLinearEquiv (he : ∀ g, ‖g‖ = wNorm (e g)) :
    G ≃L[𝕜] C₀(ℕ, β) :=
  e.toContinuousLinearEquivOfBounds 1 (3 / 2)
    (fun g => by simpa using (model_norm_bounds e he g).1)
    (fun x => by simpa using (model_norm_bounds e he (e.symm x)).2)

/-- A model is complete when `β` is. -/
theorem model_completeSpace [CompleteSpace β] (he : ∀ g, ‖g‖ = wNorm (e g)) :
    CompleteSpace G := by
  let ψ := modelContinuousLinearEquiv e he
  exact (ψ.isUniformEmbedding.isUniformInducing.completeSpace_congr ψ.surjective).mpr
    inferInstance

end AlternatingAnalytic.WeightedNorm
