import AlternatingAnalytic.Analysis.SphericalCompleteness
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Algebra.Algebra.Bilinear
import AlternatingAnalytic.Analysis.ProjectiveBaseChange
import AlternatingAnalytic.Analysis.CompletedBaseChange
import AlternatingAnalytic.Analysis.DenseMultilinearExtension

/-!
# Proof of Lemma D.6

Uses the projective base change of `AlternatingAnalytic/Analysis/ProjectiveBaseChange.lean`
(`projNorm` is `baseChangeSeminorm` by `baseChangeSeminorm_eq_iInf`) and, for part (4),
`denseLinearExtension` of `scalarContractionContinuous ϖ`.
-/

open scoped TensorProduct

namespace AlternatingAnalyticChallenge.LemD_6

universe u₁ u uW

section Definitions

variable (K₁ : Type u₁) (V K' : Type u) [NontriviallyNormedField K₁]
  [NormedAddCommGroup V] [NormedSpace K₁ V] [NormedField K'] [NormedAlgebra K₁ K']

/-- The projective norm `‖u‖_π = inf ∑ⱼ ‖xⱼ‖ ‖λⱼ‖` over finite decompositions
`u = ∑ⱼ xⱼ ⊗ λⱼ`. -/
noncomputable def projNorm (u : V ⊗[K₁] K') : ℝ :=
  ⨅ s : {s : List (V × K') // (s.map fun z => z.1 ⊗ₜ[K₁] z.2).sum = u},
    (s.val.map fun z => ‖z.1‖ * ‖z.2‖).sum

variable {K₁ V K'}

/-- `T_ψ : V_{K′} → V`, the `K₁`-linear map with `T_ψ (x ⊗ λ) = ψ(λ) x`. -/
noncomputable def contraction (ψ : K' →ₗ[K₁] K₁) : V ⊗[K₁] K' →ₗ[K₁] V :=
  (TensorProduct.rid K₁ V).toLinearMap.comp (ψ.lTensor V)

variable (V)

/-- Multiplication by `μ ∈ K′` on `V_{K′}` through the second factor, `x ⊗ λ ↦ x ⊗ μλ`. -/
noncomputable def scaleRight (μ : K') : V ⊗[K₁] K' →ₗ[K₁] V ⊗[K₁] K' :=
  (LinearMap.mulLeft K₁ μ).lTensor V

end Definitions

variable {K₁ : Type u₁} {V K' : Type u} [NontriviallyNormedField K₁] [CompleteSpace K₁]
  [SphericallyCompleteSpace K₁] [NormedAddCommGroup V] [NormedSpace K₁ V]
  [NormedField K'] [NormedAlgebra K₁ K'] [IsUltrametricDist K']

private theorem ultrametric_of_normedAlgebra (A B : Type*) [NontriviallyNormedField A]
    [NormedField B] [NormedAlgebra A B] [IsUltrametricDist B] : IsUltrametricDist A :=
  ⟨fun x y z => by
    simpa only [dist_eq_norm, ← map_sub, norm_algebraMap'] using
      IsUltrametricDist.dist_triangle_max (algebraMap A B x) (algebraMap A B y)
        (algebraMap A B z)⟩

omit [CompleteSpace K₁] [SphericallyCompleteSpace K₁] [IsUltrametricDist K'] in
private theorem projNorm_eq (u : V ⊗[K₁] K') :
    projNorm K₁ V K' u = AlternatingAnalytic.baseChangeSeminorm K₁ V K' u :=
  (AlternatingAnalytic.baseChangeSeminorm_eq_iInf K₁ V K' u).symm

/-- `‖T_ψ u‖ ≤ ‖ψ‖ ‖u‖_π` for every bounded `K₁`-linear `ψ : K′ → K₁`. -/
theorem part1 (ψ : K' →L[K₁] K₁) (u : V ⊗[K₁] K') :
    ‖contraction ψ.toLinearMap u‖ ≤ ‖ψ‖ * projNorm K₁ V K' u := by
  rw [projNorm_eq]
  exact AlternatingAnalytic.norm_scalarContraction_le ψ u

/-- `‖·‖_π` is a `K′`-norm on `V_{K′}`: nonnegative, zero only at zero, subadditive, and
homogeneous for the `K′`-action through the second factor. -/
theorem part2 :
    (∀ u : V ⊗[K₁] K', 0 ≤ projNorm K₁ V K' u) ∧
      (∀ u : V ⊗[K₁] K', projNorm K₁ V K' u = 0 ↔ u = 0) ∧
      (∀ u v : V ⊗[K₁] K', projNorm K₁ V K' (u + v) ≤ projNorm K₁ V K' u + projNorm K₁ V K' v) ∧
      ∀ (μ : K') (u : V ⊗[K₁] K'),
        projNorm K₁ V K' (scaleRight V μ u) = ‖μ‖ * projNorm K₁ V K' u := by
  have := ultrametric_of_normedAlgebra K₁ K'
  refine ⟨fun u => ?_, fun u => ?_, fun u v => ?_, fun μ u => ?_⟩
  · rw [projNorm_eq]; exact apply_nonneg _ u
  · rw [projNorm_eq]; exact AlternatingAnalytic.baseChangeSeminorm_eq_zero_iff u
  · rw [projNorm_eq, projNorm_eq, projNorm_eq]; exact map_add_le_add _ u v
  · letI := AlternatingAnalytic.baseChangeModule K₁ V K'
    rw [projNorm_eq, projNorm_eq]
    change AlternatingAnalytic.baseChangeSeminorm K₁ V K'
      (AlternatingAnalytic.baseChangeScalarMap K₁ V K' μ u) = _
    rw [AlternatingAnalytic.baseChangeScalarMap_apply,
      AlternatingAnalytic.baseChangeSeminorm_smul]

/-- The map `x ↦ x ⊗ 1` is an isometry for `‖·‖_π`. -/
theorem part3 (x : V) : projNorm K₁ V K' (x ⊗ₜ[K₁] (1 : K')) = ‖x‖ := by
  have := ultrametric_of_normedAlgebra K₁ K'
  rw [projNorm_eq]
  exact AlternatingAnalytic.baseChangeSeminorm_tmul_one K₁ V K' x

/-- If `V` is complete, `T_ϖ` extends to `Π_V` on the completion with `‖Π_V‖ ≤ 1` and
`Π_V ∘ ι_V = id`. The completion is any complete `W` with a dense-range `‖·‖_π`-isometry `j`. -/
theorem part4 [CompleteSpace V]
    (ϖ : K' →ₗ[K₁] K₁) (hϖfix : ∀ c : K₁, ϖ (algebraMap K₁ K' c) = c)
    (hϖle : ∀ l : K', ‖ϖ l‖ ≤ ‖l‖)
    {W : Type uW} [NormedAddCommGroup W] [NormedSpace K₁ W] [CompleteSpace W]
    (j : V ⊗[K₁] K' →ₗ[K₁] W) (hj : ∀ u, ‖j u‖ = projNorm K₁ V K' u) (hjd : DenseRange j) :
    ∃ P : W →L[K₁] V, ‖P‖ ≤ 1 ∧ (∀ u, P (j u) = contraction ϖ u) ∧
      ∀ x : V, P (j (x ⊗ₜ[K₁] (1 : K'))) = x := by
  have := ultrametric_of_normedAlgebra K₁ K'
  letI := AlternatingAnalytic.baseChangeNormedAddCommGroup K₁ V K'
  letI := AlternatingAnalytic.baseChangeNormedSpaceRestrictScalars K₁ V K'
  let ϖc : K' →L[K₁] K₁ := ϖ.mkContinuous 1 (fun l => by simpa using hϖle l)
  have hϖc : ‖ϖc‖ ≤ 1 := LinearMap.mkContinuous_norm_le _ zero_le_one _
  let J : V ⊗[K₁] K' →ₗᵢ[K₁] W :=
    { toLinearMap := j
      norm_map' := fun u => (hj u).trans (projNorm_eq u) }
  have hJd : DenseRange J := hjd
  let T := AlternatingAnalytic.scalarContractionContinuous K₁ V K' ϖc
  have hT : ‖T‖ ≤ ‖ϖc‖ := LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _
  let P := AlternatingAnalytic.denseLinearExtension J hJd T
  have hP : ∀ u, P (j u) = contraction ϖ u := fun u =>
    AlternatingAnalytic.denseLinearExtension_apply J hJd T u
  refine ⟨P, ((AlternatingAnalytic.norm_denseLinearExtension_le J hJd T).trans hT).trans hϖc,
    hP, fun x => ?_⟩
  have hone : ϖ 1 = 1 := by simpa using hϖfix 1
  rw [hP]
  simp [contraction, hone]

end AlternatingAnalyticChallenge.LemD_6
