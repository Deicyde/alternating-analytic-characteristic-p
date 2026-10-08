import AlternatingAnalytic.Analysis.CompletedBaseChange

/-!
# Lemma D.7 (operators), p. 44

Paper statement (Appendix D, "Projective base change"). Assume (H1) `K₁` with the restricted
absolute value is nontrivially normed, complete and spherically complete, and (H2) `K' ⊇ K₁` is
nonarchimedean. Let `E₁` be a normed `K₁`-space and `E := E₁ ⊗̂_π K'` the completion of
`(E₁ ⊗_{K₁} K', ‖·‖_π)`, with `ι_E : E₁ → E`, `x ↦ x ⊗ 1`.

"For `f ∈ L_{K₁}(E₁, E₁)` the map `f ⊗ id` on `(E₁)_{K'}` is `K'`-linear with
`‖(f ⊗ id) u‖_π ≤ ‖f‖ ‖u‖_π`. Its extension `f_{K'} ∈ L_{K'}(E, E)` satisfies `‖f_{K'}‖ ≤ ‖f‖`
and `f_{K'} ∘ ι_E = ι_E ∘ f`, and `f ↦ f_{K'}` is `K₁`-linear."

## Formalization notes

* The projective base change is the library's construction, imported as a definition:
  `E₁ ⊗[K₁] K'` with the projective norm `‖·‖_π` (local instances `baseChangeModule`,
  `baseChangeNormedAddCommGroup`, `baseChangeNormedSpace`, ... from
  `AlternatingAnalytic.Analysis.ProjectiveBaseChange`), its completion
  `CompletedBaseChange K₁ E₁ K'`, the dense inclusion `baseChangeToCompletionK` and
  `ι_E = completedBaseChangeEmbedding`. The module `CompletedBaseChange` is imported only for
  these definitions; the operator construction (`BaseChangeOperators.lean`) is not imported.
* `K₁ ⊆ K'` with the restricted absolute value is `[NormedAlgebra K₁ K']` (isometric scalar
  inclusion). (H1) is `[CompleteSpace K₁] [SphericallyCompleteSpace K₁]`; (H2) is
  `[IsUltrametricDist K']`. The library's norm on the algebraic tensor product also requires
  `[IsUltrametricDist K₁]`, which follows from (H2) and the isometric inclusion, so this adds no
  real hypothesis.
* `K'` is taken `NontriviallyNormedField` (automatic: it contains the nontrivially normed `K₁`
  isometrically).
* `E₁` and `K'` live in the same universe `u` (required by the library construction).
* Part 1 is the algebraic statement (`f ⊗ id = LinearMap.rTensor K' f` is `K'`-linear and
  `π`-bounded). Part 2 asserts the existence of a `K₁`-linear family `Φ f = f_{K'}` of continuous
  `K'`-linear operators on `E` that extend `f ⊗ id` from the dense algebraic tensor product, with
  `‖f_{K'}‖ ≤ ‖f‖` and `f_{K'} ∘ ι_E = ι_E ∘ f`.
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
    ∀ u : E₁ ⊗[K₁] K', ‖f.toLinearMap.rTensor K' u‖ ≤ ‖f‖ * ‖u‖ := by
  sorry

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
            completedBaseChangeEmbedding K₁ E₁ K' (f x) := by
  sorry

end AlternatingAnalyticChallenge.LemD_7
