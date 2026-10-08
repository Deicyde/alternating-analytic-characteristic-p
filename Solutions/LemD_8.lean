import AlternatingAnalytic.Analysis.BaseChangeAlternatingForms
import Mathlib.Analysis.Normed.Module.Alternating.Basic

/-!
# Lemma D.8 (forms), pp. 44-45

Solution: the statement of `Challenges/LemD_8.lean`, proved from
`AlternatingAnalytic/Analysis/BaseChangeAlternatingForms.lean` (strong alternation comes from
`alternating_of_baseChangeEmbedding` in `BaseChangeAlternatingCriterion.lean`).
-/

namespace AlternatingAnalyticChallenge.LemD_8

open AlternatingAnalytic

universe u

/-- Lemma D.8: every continuous alternating `K₁`-form extends `K₁`-linearly to a continuous
alternating `K'`-form on the completed base change, without increasing its norm and compatibly
with the embeddings `ι_E`, `ι_F`. -/
theorem exists_baseChangeAlternatingForms
    (K₁ : Type*) (E₁ F₁ K' : Type u) [NontriviallyNormedField K₁] [CompleteSpace K₁]
    [IsUltrametricDist K₁] [SphericallyCompleteSpace K₁]
    [NontriviallyNormedField K'] [NormedAlgebra K₁ K'] [IsUltrametricDist K']
    [NormedAddCommGroup E₁] [NormedSpace K₁ E₁]
    [NormedAddCommGroup F₁] [NormedSpace K₁ F₁] [CompleteSpace F₁] (k : ℕ) :
    ∃ Φ : (E₁ [⋀^Fin k]→L[K₁] F₁) →ₗ[K₁]
        (CompletedBaseChange K₁ E₁ K' [⋀^Fin k]→L[K'] CompletedBaseChange K₁ F₁ K'),
      ∀ m : E₁ [⋀^Fin k]→L[K₁] F₁,
        ‖Φ m‖ ≤ ‖m‖ ∧
        ∀ x : Fin k → E₁,
          Φ m (fun i => completedBaseChangeEmbedding K₁ E₁ K' (x i)) =
            completedBaseChangeEmbedding K₁ F₁ K' (m x) :=
  ⟨(baseChangeAlternatingForms K₁ E₁ F₁ K' k).toLinearMap, fun m =>
    ⟨norm_baseChangeAlternatingForms_apply_le K₁ E₁ F₁ K' k m,
      baseChangeAlternatingForms_embedding K₁ E₁ F₁ K' k m⟩⟩

end AlternatingAnalyticChallenge.LemD_8
