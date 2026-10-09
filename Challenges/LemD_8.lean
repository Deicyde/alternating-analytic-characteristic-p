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
`K₁`-linear."

## Formalization notes

* `Alt^k` is Mathlib's `ContinuousAlternatingMap` indexed by `Fin k`; it vanishes whenever two
  arguments coincide.
* `CompletedBaseChange K₁ V K'` and `ι_V = completedBaseChangeEmbedding K₁ V K'` are library
  definitions from `AlternatingAnalytic/Analysis/CompletedBaseChange.lean`.
* `K₁ ⊆ K'` is `[NormedAlgebra K₁ K']`; (H1) is `[CompleteSpace K₁] [SphericallyCompleteSpace K₁]`;
  (H2) is `[IsUltrametricDist K']`. The library also needs `[IsUltrametricDist K₁]`, which
  follows from (H2).
* `K'` is a `NontriviallyNormedField`; this follows from containing `K₁` isometrically.
* `E₁`, `F₁` and `K'` lie in one universe.
* `m_{K'}` is determined by the embedding identity, so stating only existence loses nothing.
* `K₁`-linearity of `m ↦ m_{K'}` is expressed by a `K₁`-linear map `Φ`.
-/

namespace AlternatingAnalyticChallenge.LemD_8

open AlternatingAnalytic

universe u

/-- Every continuous alternating `K₁`-form `m` extends to a continuous alternating `K'`-form
`m_{K'}` on the completed base changes, with `‖m_{K'}‖ ≤ ‖m‖`, `K₁`-linearly in `m`. -/
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
