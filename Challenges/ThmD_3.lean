import AlternatingAnalytic.Analysis.SphericalCompleteness

/-!
# Theorem D.3 (Ingleton), p. 43

Paper statement: "Let K₁ be a spherically complete nonarchimedean normed field, V a
K₁-vector space with a nonarchimedean norm, V₀ ⊆ V a subspace, C ≥ 0, and T₀ : V₀ → K₁
linear with |T₀ v| ≤ C‖v‖ for v ∈ V₀. Then T₀ extends to a linear map T : V → K₁ with
|T x| ≤ C‖x‖ for all x ∈ V."

Formalization notes:
* `K₁` is a `NontriviallyNormedField` (the paper says "normed field"; in Appendix D the
  field is nontrivially normed by (H1)). The theorem sits inside the paper's scope "Throughout
  the rest of this section we fix K₁ ⊆ K′ with (H1)" and reuses that symbol `K₁`, so the
  nontrivial norm is taken from (H1). The trivially normed case, where Ingleton's theorem
  still holds, is not covered. Completeness of `K₁` from (H1) is not assumed.
* "Nonarchimedean" is `IsUltrametricDist` on `K₁` and on `V`; "V a K₁-vector space with a
  nonarchimedean norm" is `NormedAddCommGroup V`, `NormedSpace K₁ V`, `IsUltrametricDist V`.
* Spherical completeness is the library class `SphericallyCompleteSpace`
  (`AlternatingAnalytic/Analysis/SphericalCompleteness.lean`). That module is imported for
  this definition; it also contains the library's proof of the theorem
  (`exists_extension_of_sphericallyComplete`), which the statement does not use.
* `V₀` is a `Submodule K₁ V`; `T₀ : V₀ →ₗ[K₁] K₁`; the extension `T` is a `K₁`-linear map
  (`V →ₗ[K₁] K₁`), as in the paper; its continuity follows from the bound.
* Universes of `K₁` and `V` are independent.
* No definitions are introduced.
-/

namespace AlternatingAnalyticChallenge.ThmD_3

universe uK uV

/-- **Theorem D.3 (Ingleton).** Over a spherically complete ultrametric field, a linear
functional on a subspace of an ultrametric normed space bounded by `C ‖·‖` extends to a linear
functional on the whole space with the same bound. -/
theorem ingleton_extension
    {K₁ : Type uK} [NontriviallyNormedField K₁] [IsUltrametricDist K₁]
    [SphericallyCompleteSpace K₁]
    {V : Type uV} [NormedAddCommGroup V] [NormedSpace K₁ V] [IsUltrametricDist V]
    (V₀ : Submodule K₁ V) (C : ℝ) (hC : 0 ≤ C) (T₀ : V₀ →ₗ[K₁] K₁)
    (hT₀ : ∀ v : V₀, ‖T₀ v‖ ≤ C * ‖(v : V)‖) :
    ∃ T : V →ₗ[K₁] K₁, (∀ v : V₀, T v = T₀ v) ∧ ∀ x : V, ‖T x‖ ≤ C * ‖x‖ := by
  sorry

end AlternatingAnalyticChallenge.ThmD_3
