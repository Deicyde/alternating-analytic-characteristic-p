import AlternatingAnalytic.Analysis.SphericalCompleteness
import AlternatingAnalytic.Analysis.ScalarProjection

/-!
# Corollary D.4 (Ingleton projection), p. 43

Solution: the statement of `Challenges/CorD_4.lean`, proved from the library theorem
`AlternatingAnalytic.exists_scalar_projection`
(`AlternatingAnalytic/Analysis/ScalarProjection.lean`). The library also assumes
`IsUltrametricDist K₁`; it is derived here from (H2) through the isometric `algebraMap`.
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
  have : IsUltrametricDist K₁ := ⟨fun x y z => by
    simpa only [dist_eq_norm, ← map_sub, norm_algebraMap'] using
      IsUltrametricDist.dist_triangle_max (algebraMap K₁ K' x) (algebraMap K₁ K' y)
        (algebraMap K₁ K' z)⟩
  obtain ⟨π, hπ, hfix⟩ := AlternatingAnalytic.exists_scalar_projection K₁ K'
  refine ⟨π.toLinearMap, hfix, fun l => ?_⟩
  calc ‖π l‖ ≤ ‖π‖ * ‖l‖ := π.le_opNorm l
    _ ≤ 1 * ‖l‖ := mul_le_mul_of_nonneg_right hπ (norm_nonneg l)
    _ = ‖l‖ := one_mul _

end AlternatingAnalyticChallenge.CorD_4
