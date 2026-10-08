import AlternatingAnalytic.Analysis.DiscreteSphericalCompleteness
import AlternatingAnalytic.Analysis.DiscreteSupNorm
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# Spherical completeness of `c₀(ℕ, K)` and contracting retractions onto it

For an ultrametric normed group `K`, the supremum norm on `C₀(α, K)` is ultrametric. If moreover
`K` is complete with nonzero norms in `e ^ ℤ` (`e > 1`), then every nonzero element of `C₀(ℕ, K)`
attains its norm, so all nonzero distances lie in `e ^ ℤ` and `C₀(ℕ, K)` is spherically complete
(`sphericallyCompleteSpace_of_discreteDist`). Ingleton's extension theorem
(`exists_extension_of_sphericallyComplete`) then gives a contracting left inverse to every linear
isometry of a spherically complete space into an ultrametric normed space.
-/

open scoped ZeroAtInfty BoundedContinuousFunction

namespace AlternatingAnalytic.FiniteDimSharp

section CZero

variable {α K : Type*} [TopologicalSpace α] [NormedAddCommGroup K]

/-- Each value of `f ∈ C₀(α, K)` is bounded by the supremum norm. -/
theorem norm_apply_le_norm_cZero (f : C₀(α, K)) (x : α) : ‖f x‖ ≤ ‖f‖ :=
  (f.toBCF.norm_coe_le_norm x).trans_eq ZeroAtInftyContinuousMap.norm_toBCF_eq_norm

/-- The supremum norm on `C₀(α, K)` is ultrametric when the norm of `K` is. -/
instance isUltrametricDist_cZero [IsUltrametricDist K] : IsUltrametricDist C₀(α, K) := by
  refine IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun f g => ?_
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  refine (BoundedContinuousFunction.norm_le (le_max_of_le_left (norm_nonneg f))).2 fun x => ?_
  exact (IsUltrametricDist.norm_add_le_max (f x) (g x)).trans
    (max_le_max (norm_apply_le_norm_cZero f x) (norm_apply_le_norm_cZero g x))

/-- Over a complete ultrametric `K` whose nonzero norms are integral powers of `e > 1`, the space
`C₀(ℕ, K)` is spherically complete. -/
theorem sphericallyCompleteSpace_cZero [IsUltrametricDist K] [CompleteSpace K] {e : ℝ}
    (he : 1 < e) (hval : ∀ y : K, y ≠ 0 → ∃ n : ℤ, ‖y‖ = e ^ n) :
    SphericallyCompleteSpace C₀(ℕ, K) := by
  refine sphericallyCompleteSpace_of_discreteDist he fun f g hfg => ?_
  have hne : (f - g).toBCF ≠ 0 := by
    intro h
    apply hfg
    rw [← sub_eq_zero]
    ext n
    exact congrArg (fun φ : ℕ →ᵇ K => φ n) h
  obtain ⟨s, hs, hnorm⟩ := exists_norm_eq_of_discrete e he hval (f - g).toBCF hne
  rw [dist_eq_norm, ← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm, hnorm]
  exact hval _ hs

end CZero

section Retraction

variable {K X Y : Type*} [NontriviallyNormedField K]
  [SeminormedAddCommGroup X] [NormedSpace K X] [IsUltrametricDist X]
  [NormedAddCommGroup Y] [NormedSpace K Y] [IsUltrametricDist Y] [SphericallyCompleteSpace Y]

/-- A linear isometry of a spherically complete space into an ultrametric normed space has a
continuous linear left inverse of norm at most one. -/
theorem exists_retraction_of_linearIsometry (i : Y →ₗᵢ[K] X) :
    ∃ π : X →L[K] Y, ‖π‖ ≤ 1 ∧ ∀ y : Y, π (i y) = y := by
  let D : Submodule K X := LinearMap.range i.toLinearMap
  let e : Y ≃ₗᵢ[K] D := i.equivRange
  let T₀ : D →ₗ[K] Y := e.symm.toLinearEquiv.toLinearMap
  have hT₀ : ∀ d : D, ‖T₀ d‖ ≤ ‖(d : X)‖ := fun d => (e.symm.norm_map d).le
  obtain ⟨π, hπ, hbound⟩ := exists_extension_of_sphericallyComplete
    ({((0 : X →L[K] Y), (1 : ℝ))} : Set ((X →L[K] Y) × ℝ))
    (Set.singleton_nonempty _)
    (by
      rintro p hp q hq
      rcases Set.mem_singleton_iff.mp hp with rfl
      rcases Set.mem_singleton_iff.mp hq with rfl
      norm_num)
    D T₀ (by
      rintro p hp d
      rcases Set.mem_singleton_iff.mp hp with rfl
      simpa using hT₀ d)
  refine ⟨π, π.opNorm_le_bound (by norm_num) ?_, ?_⟩
  · intro x
    simpa using hbound (0, 1) (Set.mem_singleton _) x
  · intro y
    calc
      π (i y) = π ((e y : D) : X) := rfl
      _ = T₀ (e y) := hπ (e y)
      _ = y := e.symm_apply_apply y

end Retraction

end AlternatingAnalytic.FiniteDimSharp
