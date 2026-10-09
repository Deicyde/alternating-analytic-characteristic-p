import AlternatingAnalytic.Analysis.CompletedBaseChange
import Mathlib.Analysis.Normed.Module.Alternating.Basic

/-!
# Lemma D.8 (forms), pp. 45-46

Paper statement (Appendix D). Assume (H1) `K₁` is nontrivially normed, complete and spherically
complete, and (H2) `K' ⊇ K₁` is nonarchimedean. Let `E₁` be a normed `K₁`-space, `F₁` a
`K₁`-Banach space, `E := E₁ ⊗̂_π K'`, `F := F₁ ⊗̂_π K'`, with the isometries `ι_E : E₁ → E`,
`ι_F : F₁ → F`, `x ↦ x ⊗ 1`.

"For `m ∈ Alt^k_{K₁}(E₁; F₁)` there is `m_{K'} ∈ Alt^k_{K'}(E; F)` with `‖m_{K'}‖ ≤ ‖m‖` and
`m_{K'}(ι_E x₁, …, ι_E x_k) = ι_F(m(x₁, …, x_k))` (`xᵢ ∈ E₁`), and `m ↦ m_{K'}` is
`K₁`-linear."  The proof also establishes strong alternation of `m_{K'}` (vanishing whenever two
arguments coincide), which is part of membership in `Alt^k_{K'}(E; F)`.

## Formalization notes

* `Alt^k` is Mathlib's `ContinuousAlternatingMap` with index type `Fin k`; it is strongly
  alternating by definition (vanishes on any input with two equal entries), so "strong
  alternation" is built into the codomain type.
* The completed projective base change `CompletedBaseChange K₁ V K'` and the embedding
  `ι_V = completedBaseChangeEmbedding K₁ V K'` are the library's construction, imported as
  definitions from `AlternatingAnalytic.Analysis.CompletedBaseChange`. The proving modules
  (`BaseChangeAlternatingForms.lean`, `BaseChangeAlternatingCriterion.lean`) are not imported.
* `K₁ ⊆ K'` isometrically is `[NormedAlgebra K₁ K']`; (H1) is `[CompleteSpace K₁]
  [SphericallyCompleteSpace K₁]`; (H2) is `[IsUltrametricDist K']`. `[IsUltrametricDist K₁]` is
  required by the library construction and follows from (H2).
* `K'` is taken `NontriviallyNormedField` (automatic: it contains the nontrivially normed `K₁`
  isometrically).
* `E₁`, `F₁`, `K'` live in one universe `u` (library construction).
* `m_{K'}` is uniquely determined by the stated embedding identity (the `K'`-span of `ι_E E₁` is
  dense in `E` and `m_{K'}` is continuous `K'`-multilinear), so the existential statement is not
  weaker than the paper's construction.
* `K₁`-linearity of `m ↦ m_{K'}` is expressed by asking for a `K₁`-linear map `Φ`.
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
            completedBaseChangeEmbedding K₁ F₁ K' (m x) := by
  sorry

end AlternatingAnalyticChallenge.LemD_8
