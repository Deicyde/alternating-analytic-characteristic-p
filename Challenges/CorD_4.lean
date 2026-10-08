import AlternatingAnalytic.Analysis.SphericalCompleteness

/-!
# Corollary D.4 (Ingleton projection), p. 42

Paper statement (standing hypotheses of §D.2): fix fields K₁ ⊆ K′ such that
"(H1) K₁, with the restricted absolute value, is nontrivially normed, complete and spherically
complete. (H2) K′ is nonarchimedean."
"Corollary D.4. There is a K₁-linear map ϖ : K′ → K₁ with ϖ|K₁ = id and |ϖ(λ)| ≤ |λ| for
all λ ∈ K′."

Formalization notes:
* The inclusion `K₁ ⊆ K′` with the restricted absolute value is a `NormedAlgebra K₁ K′`
  (an isometric field embedding `algebraMap K₁ K′`); `ϖ|K₁ = id` is
  `ϖ (algebraMap K₁ K′ c) = c`.
* (H1): `NontriviallyNormedField K₁`, `CompleteSpace K₁`, `SphericallyCompleteSpace K₁`.
  Completeness of `K₁` is kept as in (H1) although the proof does not use it.
  (H2): `NormedField K′` with `IsUltrametricDist K′`. No ultrametric hypothesis is put on
  `K₁`; it follows from (H2) through the isometric inclusion.
* Spherical completeness is the library class `SphericallyCompleteSpace`
  (`AlternatingAnalytic/Analysis/SphericalCompleteness.lean`), imported for this definition.
* `ϖ` is a `K₁`-linear map `K′ →ₗ[K₁] K₁`; the contraction `|ϖ λ| ≤ |λ|` is stated pointwise.
* Universes of `K₁` and `K′` are independent.
* No definitions are introduced.
-/

namespace AlternatingAnalyticChallenge.CorD_4

universe u₁ u'

/-- **Corollary D.4 (Ingleton projection).** Under (H1) and (H2) there is a `K₁`-linear map
`ϖ : K′ → K₁` with `ϖ|K₁ = id` and `|ϖ(λ)| ≤ |λ|`. -/
theorem ingleton_projection
    (K₁ : Type u₁) (K' : Type u') [NontriviallyNormedField K₁] [CompleteSpace K₁]
    [SphericallyCompleteSpace K₁] [NormedField K'] [NormedAlgebra K₁ K']
    [IsUltrametricDist K'] :
    ∃ ϖ : K' →ₗ[K₁] K₁, (∀ c : K₁, ϖ (algebraMap K₁ K' c) = c) ∧
      ∀ l : K', ‖ϖ l‖ ≤ ‖l‖ := by
  sorry

end AlternatingAnalyticChallenge.CorD_4
