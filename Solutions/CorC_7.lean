import AlternatingAnalytic.Analysis.LaurentField
import AlternatingAnalytic.Analysis.ProjectiveExterior
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import AlternatingAnalytic.Laurent.DiagonalTransitions
import AlternatingAnalytic.Laurent.CZeroMultipliers.Analytic

/-!
# Proof of Corollary C.7

Part 1 is `DiagonalTransitions.laurent_part1` and part 2 is
`DiagonalTransitions.not_analyticAt_wedge_mul_one_add` (`Laurent/DiagonalTransitions.lean`)
applied to `czero_not_analyticAt_precomp_wedge` (Proposition C.6) at `u₀ = id`.
-/

set_option backward.isDefEq.respectTransparency false

open scoped NNReal BoundedContinuousFunction ZeroAtInfty

namespace AlternatingAnalyticChallenge.CorC_7

open AlternatingAnalytic

universe u

/-- The transition `D_{1+a} ∈ L(E₁, E₁)` between the trivializations `τ₀` and `τ₁` at
`a ∈ c₀(ℕ, K₁)`: coordinatewise multiplication by `1 + a`. -/
noncomputable def transition (κ : Type u) [Field κ] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)]
    (a : C₀(ℕ, LaurentField κ r)) :
    (ℕ →ᵇ LaurentField κ r) →L[LaurentField κ r] (ℕ →ᵇ LaurentField κ r) :=
  ContinuousLinearMap.mul (LaurentField κ r) (ℕ →ᵇ LaurentField κ r) (1 + a.toBCF)

/-- On the open unit ball `U` of `c₀(ℕ, K₁)` the transitions `D_{1+a}` are isometric
automorphisms of `E₁`, and the transition and its inverse are analytic on `U`. -/
theorem part1_analytic_isometric_transitions
    (κ : Type u) [Field κ] [Finite κ] (p : ℕ) (hp : p.Prime) [CharP κ p]
    (k : ℕ) (hpk : p ≤ k) (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] :
    (∀ a ∈ Metric.ball (0 : C₀(ℕ, LaurentField κ r)) 1, ∀ z : ℕ →ᵇ LaurentField κ r,
      ‖transition κ r a z‖ = ‖z‖) ∧
    (∀ a ∈ Metric.ball (0 : C₀(ℕ, LaurentField κ r)) 1, IsUnit (transition κ r a)) ∧
    AnalyticOnNhd (LaurentField κ r) (transition κ r)
      (Metric.ball (0 : C₀(ℕ, LaurentField κ r)) 1) ∧
    AnalyticOnNhd (LaurentField κ r) (fun a => Ring.inverse (transition κ r a))
      (Metric.ball (0 : C₀(ℕ, LaurentField κ r)) 1) :=
  DiagonalTransitions.laurent_part1 κ r

/-- The map `a ↦ W_B ∘ (D_{1+a}, …, D_{1+a})` (the section constantly `W_B` in the `τ₁` chart,
read in the `τ₀` chart) is analytic at no point of `U`. -/
theorem part2_not_analyticAt
    (κ : Type u) [Field κ] [Finite κ] (p : ℕ) (hp : p.Prime) [CharP κ p]
    (k : ℕ) (hpk : p ≤ k) (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] :
    ∀ a₀ ∈ Metric.ball (0 : C₀(ℕ, LaurentField κ r)) 1,
      ¬ AnalyticAt (LaurentField κ r)
        (fun a : C₀(ℕ, LaurentField κ r) =>
          (completedExteriorWedge (LaurentField κ r) ℕ k).compContinuousLinearMap
            (transition κ r a)) a₀ := by
  have : Fact p.Prime := ⟨hp⟩
  exact DiagonalTransitions.not_analyticAt_wedge_mul_one_add κ r k
    (fun u₀ a₀ => czero_not_analyticAt_precomp_wedge κ r k p hpk u₀ a₀)

end AlternatingAnalyticChallenge.CorC_7
