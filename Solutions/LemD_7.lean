import AlternatingAnalytic.Analysis.BaseChangeOperators

/-!
# Lemma D.7 (operators), p. 44

Solution: the statements of `Challenges/LemD_7.lean`, proved from
`AlternatingAnalytic/Analysis/BaseChangeOperators.lean`.
-/

open scoped TensorProduct

namespace AlternatingAnalyticChallenge.LemD_7

open AlternatingAnalytic

universe u

attribute [local instance] baseChangeModule baseChangeNormedAddCommGroup
  baseChangeNormedSpaceRestrictScalars baseChangeNormedSpace baseChangeIsScalarTower

/-- Lemma D.7, algebraic part: `f ⊗ id` is `K'`-linear on `E₁ ⊗[K₁] K'` and bounded by `‖f‖`
for the projective norm. -/
theorem baseChangeOperator_algebraic
    (K₁ : Type*) (E₁ K' : Type u) [NontriviallyNormedField K₁] [CompleteSpace K₁]
    [IsUltrametricDist K₁] [SphericallyCompleteSpace K₁]
    [NontriviallyNormedField K'] [NormedAlgebra K₁ K'] [IsUltrametricDist K']
    [NormedAddCommGroup E₁] [NormedSpace K₁ E₁] (f : E₁ →L[K₁] E₁) :
    (∀ (a : K') (u : E₁ ⊗[K₁] K'),
        f.toLinearMap.rTensor K' (a • u) = a • f.toLinearMap.rTensor K' u) ∧
    ∀ u : E₁ ⊗[K₁] K', ‖f.toLinearMap.rTensor K' u‖ ≤ ‖f‖ * ‖u‖ :=
  ⟨(baseChangeOperatorAlgebraic K₁ E₁ K' f).map_smul,
    norm_baseChangeOperatorAlgebraic_apply_le K₁ E₁ K' f⟩

/-- Lemma D.7, completed part: a `K₁`-linear family `f ↦ f_{K'}` of continuous `K'`-linear
extensions of `f ⊗ id` to the completion, with `‖f_{K'}‖ ≤ ‖f‖` and `f_{K'} ∘ ι_E = ι_E ∘ f`. -/
theorem exists_completedBaseChangeOperator
    (K₁ : Type*) (E₁ K' : Type u) [NontriviallyNormedField K₁] [CompleteSpace K₁]
    [IsUltrametricDist K₁] [SphericallyCompleteSpace K₁]
    [NontriviallyNormedField K'] [NormedAlgebra K₁ K'] [IsUltrametricDist K']
    [NormedAddCommGroup E₁] [NormedSpace K₁ E₁] :
    ∃ Φ : (E₁ →L[K₁] E₁) →ₗ[K₁]
        (CompletedBaseChange K₁ E₁ K' →L[K'] CompletedBaseChange K₁ E₁ K'),
      ∀ f : E₁ →L[K₁] E₁,
        (∀ u : E₁ ⊗[K₁] K', Φ f (baseChangeToCompletionK K₁ E₁ K' u) =
            baseChangeToCompletionK K₁ E₁ K' (f.toLinearMap.rTensor K' u)) ∧
        ‖Φ f‖ ≤ ‖f‖ ∧
        ∀ x : E₁, Φ f (completedBaseChangeEmbedding K₁ E₁ K' x) =
            completedBaseChangeEmbedding K₁ E₁ K' (f x) :=
  ⟨baseChangeOperatorsLinear K₁ E₁ K', fun f =>
    ⟨completedBaseChangeOperator_apply_tensor K₁ E₁ K' f,
      norm_completedBaseChangeOperator_le K₁ E₁ K' f,
      completedBaseChangeOperator_embedding K₁ E₁ K' f⟩⟩

end AlternatingAnalyticChallenge.LemD_7
