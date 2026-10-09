import AlternatingAnalytic.Analysis.SphericalCompleteness

/-!
# Theorem D.3 (Ingleton), p. 43

Paper statement: "Let K₁ be a spherically complete nonarchimedean normed field, V a
K₁-vector space with a nonarchimedean norm, V₀ ⊆ V a subspace, C ≥ 0, and T₀ : V₀ → K₁
linear with |T₀ v| ≤ C‖v‖ for v ∈ V₀. Then T₀ extends to a linear map T : V → K₁ with
|T x| ≤ C‖x‖ for all x ∈ V."

## Formalization notes

* `K₁` is a `NontriviallyNormedField`, as in the standing hypothesis (H1) of Appendix D, so the
  trivially normed case is not covered. Completeness of `K₁` is not assumed.
* "Nonarchimedean" is `IsUltrametricDist` on `K₁` and on `V`.
* Spherical completeness is the library class `SphericallyCompleteSpace`
  (`AlternatingAnalytic/Analysis/SphericalCompleteness.lean`).
* `V₀` is a `Submodule K₁ V`; `T₀` and `T` are `K₁`-linear maps.
-/

namespace AlternatingAnalyticChallenge.ThmD_3

universe uK uV

/-- Ingleton's theorem: over a spherically complete ultrametric field, a linear functional on
a subspace with `‖T₀ v‖ ≤ C ‖v‖` extends to the whole space with the same bound. -/
theorem ingleton_extension
    {K₁ : Type uK} [NontriviallyNormedField K₁] [IsUltrametricDist K₁]
    [SphericallyCompleteSpace K₁]
    {V : Type uV} [NormedAddCommGroup V] [NormedSpace K₁ V] [IsUltrametricDist V]
    (V₀ : Submodule K₁ V) (C : ℝ) (hC : 0 ≤ C) (T₀ : V₀ →ₗ[K₁] K₁)
    (hT₀ : ∀ v : V₀, ‖T₀ v‖ ≤ C * ‖(v : V)‖) :
    ∃ T : V →ₗ[K₁] K₁, (∀ v : V₀, T v = T₀ v) ∧ ∀ x : V, ‖T x‖ ≤ C * ‖x‖ := by
  sorry

end AlternatingAnalyticChallenge.ThmD_3
