import AlternatingAnalytic.Analysis.LaurentField
import AlternatingAnalytic.Analysis.ProjectiveExterior
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import AlternatingAnalytic.Laurent.CZeroMultipliers.Analytic

/-!
# Proposition C.6 (multipliers on `c₀`), p. 40

Solution: the statements of `Challenges/PropC_6.lean`, proved from the library
(`Laurent/CZeroMultipliers/NoLift.lean`, `Laurent/CZeroMultipliers/Analytic.lean`):
* part 1: `AlternatingAnalytic.czero_not_exists_multiplierLift` (the Laurent residue of the lift
  on finitely supported coefficient-field multipliers, then `finiteField_multiplier_obstruction`);
* part 2: `AlternatingAnalytic.czero_not_analyticAt_precomp_wedge` (the degree-`k` term of a power
  series is a bounded lift, `precompAffine_coeff_eq_of_hasFPowerSeriesAt`);
* part 3: `AlternatingAnalytic.czero_not_analyticAt_precomp` (evaluation at `W_B`).
-/

set_option backward.isDefEq.respectTransparency false

open scoped NNReal BoundedContinuousFunction ZeroAtInfty

namespace AlternatingAnalyticChallenge.PropC_6

open AlternatingAnalytic

universe u

/-- `σ(a) = W_B ∘ (D_a, …, D_a)`, i.e. `σ(a)(x) = (a x₁) ∧ ⋯ ∧ (a x_k)`, for `a ∈ c₀(ℕ, K₁)`. -/
noncomputable def sigma (κ : Type u) [Field κ] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] (k : ℕ)
    (a : C₀(ℕ, LaurentField κ r)) :
    (ℕ →ᵇ LaurentField κ r) [⋀^Fin k]→L[LaurentField κ r]
      ProjectiveExteriorCompletion (LaurentField κ r) ℕ k :=
  (completedExteriorWedge (LaurentField κ r) ℕ k).compContinuousLinearMap
    (ContinuousLinearMap.mul (LaurentField κ r) (ℕ →ᵇ LaurentField κ r) a.toBCF)

/-- **Proposition C.6, main part.** `σ` has no bounded `k`-linear lift with values in
`Alt^k(E₁; B)`. -/
theorem part1_sigma_no_bounded_lift
    (κ : Type u) [Field κ] [Finite κ] (p : ℕ) (hp : p.Prime) [CharP κ p]
    (k : ℕ) (hpk : p ≤ k) (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] :
    ¬ ∃ P : ContinuousMultilinearMap (LaurentField κ r)
        (fun _ : Fin k => C₀(ℕ, LaurentField κ r))
        ((ℕ →ᵇ LaurentField κ r) [⋀^Fin k]→L[LaurentField κ r]
          ProjectiveExteriorCompletion (LaurentField κ r) ℕ k),
      ∀ a : C₀(ℕ, LaurentField κ r), P (fun _ => a) = sigma κ r k a := by
  have : Fact p.Prime := ⟨hp⟩
  exact czero_not_exists_multiplierLift κ r k p hpk

/-- **Proposition C.6, consequence.** For every `u₀`, `a ↦ A(u₀ + D_a)(W_B)` is analytic at no
point of `c₀(ℕ, K₁)`. -/
theorem part2_not_analyticAt_apply_wedge
    (κ : Type u) [Field κ] [Finite κ] (p : ℕ) (hp : p.Prime) [CharP κ p]
    (k : ℕ) (hpk : p ≤ k) (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)]
    (u₀ : (ℕ →ᵇ LaurentField κ r) →L[LaurentField κ r] (ℕ →ᵇ LaurentField κ r))
    (a₀ : C₀(ℕ, LaurentField κ r)) :
    ¬ AnalyticAt (LaurentField κ r)
      (fun a : C₀(ℕ, LaurentField κ r) =>
        ContinuousAlternatingMap.compContinuousLinearMapCLM
          (u₀ + ContinuousLinearMap.mul (LaurentField κ r) (ℕ →ᵇ LaurentField κ r) a.toBCF)
          (completedExteriorWedge (LaurentField κ r) ℕ k)) a₀ := by
  have : Fact p.Prime := ⟨hp⟩
  exact czero_not_analyticAt_precomp_wedge κ r k p hpk u₀ a₀

/-- **Proposition C.6, operator form.** For every `u₀`, `a ↦ A(u₀ + D_a)` is analytic at no
point of `c₀(ℕ, K₁)`. -/
theorem part3_not_analyticAt_operator
    (κ : Type u) [Field κ] [Finite κ] (p : ℕ) (hp : p.Prime) [CharP κ p]
    (k : ℕ) (hpk : p ≤ k) (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)]
    (u₀ : (ℕ →ᵇ LaurentField κ r) →L[LaurentField κ r] (ℕ →ᵇ LaurentField κ r))
    (a₀ : C₀(ℕ, LaurentField κ r)) :
    ¬ AnalyticAt (LaurentField κ r)
      (fun a : C₀(ℕ, LaurentField κ r) =>
        (ContinuousAlternatingMap.compContinuousLinearMapCLM
          (u₀ + ContinuousLinearMap.mul (LaurentField κ r) (ℕ →ᵇ LaurentField κ r) a.toBCF) :
          ((ℕ →ᵇ LaurentField κ r) [⋀^Fin k]→L[LaurentField κ r]
              ProjectiveExteriorCompletion (LaurentField κ r) ℕ k) →L[LaurentField κ r]
            ((ℕ →ᵇ LaurentField κ r) [⋀^Fin k]→L[LaurentField κ r]
              ProjectiveExteriorCompletion (LaurentField κ r) ℕ k))) a₀ := by
  have : Fact p.Prime := ⟨hp⟩
  exact czero_not_analyticAt_precomp κ r k p hpk u₀ a₀

end AlternatingAnalyticChallenge.PropC_6
