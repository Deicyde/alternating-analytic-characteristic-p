import AlternatingAnalytic.Analysis.CompletedBaseChange

/-!
# Lemma D.7 (operators), p. 46

Paper statement (Appendix D, "Projective base change"). Assume (H1) `K₁` with the restricted
absolute value is nontrivially normed, complete and spherically complete, and (H2) `K' ⊇ K₁` is
nonarchimedean. Let `E₁` be a normed `K₁`-space and `E := E₁ ⊗̂_π K'` the completion of
`(E₁ ⊗_{K₁} K', ‖·‖_π)`, with `ι_E : E₁ → E`, `x ↦ x ⊗ 1`.

"For `f ∈ L_{K₁}(E₁, E₁)` the map `f ⊗ id` on `(E₁)_{K'}` is `K'`-linear with
`‖(f ⊗ id) u‖_π ≤ ‖f‖ ‖u‖_π`. Its extension `f_{K'} ∈ L_{K'}(E, E)` satisfies `‖f_{K'}‖ ≤ ‖f‖`
and `f_{K'} ∘ ι_E = ι_E ∘ f`, and `f ↦ f_{K'}` is `K₁`-linear."

## Formalization notes

* `E₁ ⊗[K₁] K'` with `‖·‖_π`, its completion `CompletedBaseChange K₁ E₁ K'`, the dense map
  `baseChangeToCompletionK` and `ι_E = completedBaseChangeEmbedding` are library definitions
  (`AlternatingAnalytic/Analysis/ProjectiveBaseChange.lean`, `CompletedBaseChange.lean`), used
  through the local instances below.
* `K₁ ⊆ K'` is `[NormedAlgebra K₁ K']`; (H1) is `[CompleteSpace K₁] [SphericallyCompleteSpace K₁]`;
  (H2) is `[IsUltrametricDist K']`. The library also needs `[IsUltrametricDist K₁]`, which
  follows from (H2).
* `K'` is a `NontriviallyNormedField`; this follows from containing `K₁` isometrically.
* `E₁` and `K'` lie in one universe.
* The lemma is split in two: `f ⊗ id = f.rTensor K'` is `K'`-linear and bounded by `‖f‖`; and
  there is a `K₁`-linear family `Φ f = f_{K'}` of continuous `K'`-linear extensions to `E`.
-/

open scoped TensorProduct

namespace AlternatingAnalyticChallenge.LemD_7

open AlternatingAnalytic

universe u

attribute [local instance] baseChangeModule baseChangeNormedAddCommGroup
  baseChangeNormedSpaceRestrictScalars baseChangeNormedSpace baseChangeIsScalarTower

/-- `f ⊗ id` is `K'`-linear on `E₁ ⊗[K₁] K'` and bounded by `‖f‖` for `‖·‖_π`. -/
theorem baseChangeOperator_algebraic
    (K₁ : Type*) (E₁ K' : Type u) [NontriviallyNormedField K₁] [CompleteSpace K₁]
    [IsUltrametricDist K₁] [SphericallyCompleteSpace K₁]
    [NontriviallyNormedField K'] [NormedAlgebra K₁ K'] [IsUltrametricDist K']
    [NormedAddCommGroup E₁] [NormedSpace K₁ E₁] (f : E₁ →L[K₁] E₁) :
    (∀ (a : K') (u : E₁ ⊗[K₁] K'),
        f.toLinearMap.rTensor K' (a • u) = a • f.toLinearMap.rTensor K' u) ∧
    ∀ u : E₁ ⊗[K₁] K', ‖f.toLinearMap.rTensor K' u‖ ≤ ‖f‖ * ‖u‖ := by
  sorry

/-- There is a `K₁`-linear family `f ↦ f_{K'}` of continuous `K'`-linear operators on `E`
extending `f ⊗ id`, with `‖f_{K'}‖ ≤ ‖f‖` and `f_{K'} ∘ ι_E = ι_E ∘ f`. -/
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
            completedBaseChangeEmbedding K₁ E₁ K' (f x) := by
  sorry

end AlternatingAnalyticChallenge.LemD_7
