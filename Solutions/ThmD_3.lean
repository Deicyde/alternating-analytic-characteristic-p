import AlternatingAnalytic.Analysis.SphericalCompleteness

/-!
# Proof of Theorem D.3

Applies `exists_extension_of_sphericallyComplete`
(`AlternatingAnalytic/Analysis/SphericalCompleteness.lean`) to the single pair `(0, C)`.
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
  obtain ⟨T, hT, hbound⟩ := exists_extension_of_sphericallyComplete
    ({((0 : V →L[K₁] K₁), C)} : Set ((V →L[K₁] K₁) × ℝ)) (Set.singleton_nonempty _)
    (by
      rintro p hp q hq
      rcases Set.mem_singleton_iff.mp hp with rfl
      rcases Set.mem_singleton_iff.mp hq with rfl
      simpa using hC)
    V₀ T₀ (by
      rintro p hp d
      rcases Set.mem_singleton_iff.mp hp with rfl
      simpa using hT₀ d)
  refine ⟨T.toLinearMap, hT, fun x => ?_⟩
  simpa using hbound (0, C) (Set.mem_singleton _) x

end AlternatingAnalyticChallenge.ThmD_3
