import AlternatingAnalytic.Analysis.SphericalCompleteness

/-!
# Corollary D.4 (Ingleton projection), pp. 44-45

Paper statement (standing hypotheses of Appendix D): fix fields K₁ ⊆ K′ such that
"(H1) K₁, with the restricted absolute value, is nontrivially normed, complete and spherically
complete. (H2) K′ is nonarchimedean."
"Corollary D.4. There is a K₁-linear map ϖ : K′ → K₁ with ϖ|K₁ = id and |ϖ(λ)| ≤ |λ| for
all λ ∈ K′."

## Formalization notes

* `K₁ ⊆ K′` with the restricted absolute value is `NormedAlgebra K₁ K′`; `ϖ|K₁ = id` is
  `ϖ (algebraMap K₁ K′ c) = c`.
* (H1) is `NontriviallyNormedField K₁`, `CompleteSpace K₁`, `SphericallyCompleteSpace K₁`
  (the proof does not use completeness). (H2) is `IsUltrametricDist K′`.
-/

namespace AlternatingAnalyticChallenge.CorD_4

universe u₁ u'

/-- There is a `K₁`-linear map `ϖ : K′ → K₁` with `ϖ|K₁ = id` and `‖ϖ λ‖ ≤ ‖λ‖`. -/
theorem ingleton_projection
    (K₁ : Type u₁) (K' : Type u') [NontriviallyNormedField K₁] [CompleteSpace K₁]
    [SphericallyCompleteSpace K₁] [NormedField K'] [NormedAlgebra K₁ K']
    [IsUltrametricDist K'] :
    ∃ ϖ : K' →ₗ[K₁] K₁, (∀ c : K₁, ϖ (algebraMap K₁ K' c) = c) ∧
      ∀ l : K', ‖ϖ l‖ ≤ ‖l‖ := by
  sorry

end AlternatingAnalyticChallenge.CorD_4
