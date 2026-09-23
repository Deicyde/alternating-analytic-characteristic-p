/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
import AlternatingAnalytic.Analysis.SphericalCompleteness
import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# Contracting scalar retractions from Ingleton extension

The scalar projection in the characteristic-p paper is obtained by extending the inverse
of the scalar embedding from its range. The extension is applied only to the ultrametric
scalar domain, with the spherically complete base field as target.
-/

namespace AlternatingAnalytic

section LinearIsometry

variable {K X : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [SphericallyCompleteSpace K] [SeminormedAddCommGroup X] [NormedSpace K X]
  [IsUltrametricDist X]

/-- An isometric copy of a spherically complete scalar field in an ultrametric normed space
has a continuous linear left inverse of norm at most one. -/
theorem exists_scalar_retraction_of_linearIsometry (i : K →ₗᵢ[K] X) :
    ∃ π : X →L[K] K, ‖π‖ ≤ 1 ∧ ∀ c : K, π (i c) = c := by
  let D : Submodule K X := LinearMap.range i.toLinearMap
  let e : K ≃ₗᵢ[K] D := i.equivRange
  let T₀ : D →ₗ[K] K := e.symm.toLinearEquiv.toLinearMap
  have hT₀ : ∀ d : D, ‖T₀ d‖ ≤ ‖(d : X)‖ := fun d => (e.symm.norm_map d).le
  obtain ⟨π, hπ, hbound⟩ := exists_extension_of_sphericallyComplete
    ({((0 : X →L[K] K), (1 : ℝ))} : Set ((X →L[K] K) × ℝ))
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
  · intro c
    calc
      π (i c) = π ((e c : D) : X) := rfl
      _ = T₀ (e c) := hπ (e c)
      _ = c := e.symm_apply_apply c

end LinearIsometry

/-- Ingleton's scalar projection: an ultrametric normed field extension of a spherically
complete nontrivially normed field admits a contracting linear retraction to the base field.
Neither field is given an additional completeness hypothesis. -/
theorem exists_scalar_projection (K L : Type*) [NontriviallyNormedField K]
    [NormedField L] [NormedAlgebra K L] [IsUltrametricDist K] [IsUltrametricDist L]
    [SphericallyCompleteSpace K] :
    ∃ π : L →L[K] K, ‖π‖ ≤ 1 ∧ ∀ c : K, π (algebraMap K L c) = c := by
  let i : K →ₗᵢ[K] L :=
    { toLinearMap := Algebra.linearMap K L
      norm_map' := norm_algebraMap' L }
  exact exists_scalar_retraction_of_linearIsometry i

end AlternatingAnalytic
