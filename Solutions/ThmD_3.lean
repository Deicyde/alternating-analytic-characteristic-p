import AlternatingAnalytic.Analysis.SphericalCompleteness

/-!
# Theorem D.3 (Ingleton), p. 43

Solution: the statement of `Challenges/ThmD_3.lean`, proved from the library's master
extension lemma `exists_extension_of_sphericallyComplete`
(`AlternatingAnalytic/Analysis/SphericalCompleteness.lean`) with the single approximation
pair `S = {(0, C)}`.
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
