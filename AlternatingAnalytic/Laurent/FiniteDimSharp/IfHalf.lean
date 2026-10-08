import AlternatingAnalytic.Laurent.FiniteDimSharp.Defs
import AlternatingAnalytic.Geometry.AnalyticAlternatingBundleMorphism
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Finite-dimensional model spaces preserve analytic alternating bundles

The "if" half of Corollary C.8: over a complete nontrivially normed field, a finite-dimensional
model space `P` has continuous linear coordinates `P ≃L Fin (finrank P) → K`, so the library's
finite-coordinate theorems `contMDiffVectorBundle_alternating_of_finiteCoordinates` and
`alternatingBundleHom_of_finiteCoordinates` give both preservation properties.
-/

set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff
open Bundle

namespace AlternatingAnalytic.FiniteDimSharp

universe u

/-- A finite-dimensional model space over a complete field preserves analytic alternating
bundles and their operator-valued analytic morphisms. -/
theorem preserves_of_finiteDimensional (K : Type u) [NontriviallyNormedField K] [CompleteSpace K]
    (P : Type u) [NormedAddCommGroup P] [NormedSpace K P] [FiniteDimensional K P] (k : ℕ) :
    PreservesAnalyticBundles K P k ∧ PreservesAnalyticMorphisms K P k := by
  let c : P ≃L[K] (Fin (Module.finrank K P) → K) := ContinuousLinearEquiv.ofFinrankEq (by simp)
  refine ⟨?_, ?_⟩
  · intro M _ _ _ F₁ F₂ _ _ _ _ E₁ E₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    exact contMDiffVectorBundle_alternating_of_finiteCoordinates c k
  · intro M _ _ _ A A' B B' _ _ _ _ _ _ _ _ E E' F F'
    intros
    rename_i u v
    exact ⟨alternatingBundleHom_of_finiteCoordinates c k u v, fun b m => rfl⟩

end AlternatingAnalytic.FiniteDimSharp
