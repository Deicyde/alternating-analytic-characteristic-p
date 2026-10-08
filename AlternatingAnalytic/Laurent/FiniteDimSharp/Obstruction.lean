import AlternatingAnalytic.Analysis.LaurentField
import AlternatingAnalytic.Analysis.ProjectiveExterior
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import AlternatingAnalytic.Laurent.CZeroMultipliers.Analytic

/-!
# The `c₀` multiplier obstruction as a proposition

`CZeroOperatorObstruction κ r k` is the operator form of Proposition C.6 of the paper: over
`K₁ = κ((X))` with `|X| = r`, for every `u₀ ∈ L(E₁, E₁)`, `E₁ = ℓ^∞(ℕ, K₁)`, the map
`a ↦ A(u₀ + D_a)` on `Alt^k(E₁; B)` (`B` the completed projective exterior power, `D_a`
coordinatewise multiplication) is analytic at no point of `c₀(ℕ, K₁)`. It is stated here with the
imports of the paper's challenge file, so that its instance paths agree with that statement, and
holds for a finite `κ` of characteristic `p ≤ k` by `czero_not_analyticAt_precomp`
(`Laurent/CZeroMultipliers/Analytic.lean`).
-/

set_option backward.isDefEq.respectTransparency false

open scoped NNReal BoundedContinuousFunction ZeroAtInfty

namespace AlternatingAnalytic.FiniteDimSharp

universe u

/-- Proposition C.6, operator form: for every `u₀`, `a ↦ A(u₀ + D_a)` is analytic at no point of
`c₀(ℕ, K₁)`. -/
def CZeroOperatorObstruction (κ : Type u) [Field κ] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)]
    (k : ℕ) : Prop :=
  ∀ (u₀ : (ℕ →ᵇ LaurentField κ r) →L[LaurentField κ r] (ℕ →ᵇ LaurentField κ r))
    (a₀ : C₀(ℕ, LaurentField κ r)),
    ¬ AnalyticAt (LaurentField κ r)
      (fun a : C₀(ℕ, LaurentField κ r) =>
        (ContinuousAlternatingMap.compContinuousLinearMapCLM
          (u₀ + ContinuousLinearMap.mul (LaurentField κ r) (ℕ →ᵇ LaurentField κ r) a.toBCF) :
          ((ℕ →ᵇ LaurentField κ r) [⋀^Fin k]→L[LaurentField κ r]
              ProjectiveExteriorCompletion (LaurentField κ r) ℕ k) →L[LaurentField κ r]
            ((ℕ →ᵇ LaurentField κ r) [⋀^Fin k]→L[LaurentField κ r]
              ProjectiveExteriorCompletion (LaurentField κ r) ℕ k))) a₀

/-- Proposition C.6, operator form, holds over a finite field of characteristic `p ≤ k`. -/
theorem cZeroOperatorObstruction_of_charP (κ : Type u) [Field κ] [Finite κ] (p : ℕ)
    (hp : p.Prime) [CharP κ p] (k : ℕ) (hpk : p ≤ k) (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] :
    CZeroOperatorObstruction κ r k := fun u₀ a₀ => by
  have : Fact p.Prime := ⟨hp⟩
  exact czero_not_analyticAt_precomp κ r k p hpk u₀ a₀

end AlternatingAnalytic.FiniteDimSharp
