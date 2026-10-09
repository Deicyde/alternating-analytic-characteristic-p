import AlternatingAnalytic.Analysis.LaurentField
import AlternatingAnalytic.Analysis.ProjectiveExterior
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-!
# Proposition C.6 (multipliers on `c₀`), p. 40

Paper statement (Appendix C, §C.6, `Proposition C.6`; `κ`, `k`, `r`, `K₁`, `E₁`, `B` and `W_B` are
as in Theorem C.1, i.e. `κ` a finite field of characteristic `p`, `k ≥ p`, `r ∈ (0, 1)`,
`K₁ = κ((X))` with `|X| = r`, `E₁ = ℓ^∞(ℕ, K₁)`, `B` the completion of `Λ^k_{K₁} E₁` under the
projective exterior norm and `W_B(x) = x₁ ∧ ⋯ ∧ x_k`; `c₀(ℕ, K₁) ⊆ E₁` carries the supremum norm
and `D_a ∈ L(E₁, E₁)` denotes multiplication by `a`): The homogeneous map
`σ : c₀(ℕ, K₁) → Alt^k_{K₁}(E₁; B)`, `σ(a)(x₁,…,x_k) = W_B(a x₁,…,a x_k) = (a x₁) ∧ ⋯ ∧ (a x_k)`,
has no bounded `k`-linear lift with values in `Alt^k_{K₁}(E₁; B)`. Consequently, for every
`u₀ ∈ L(E₁, E₁)`, the map `a ↦ A^{k,K₁}_{E₁,E₁;B}(u₀ + D_a)(W_B)` is analytic at no point of
`c₀(ℕ, K₁)`. In particular `a ↦ A^{k,K₁}_{E₁,E₁;B}(u₀ + D_a)` is analytic at no point.

## Formalization notes
* Degree: index type `Fin k`. "Finite field of characteristic `p`": `[Finite κ]`, `p.Prime`,
  `[CharP κ p]`.
* `K₁ = AlternatingAnalytic.LaurentField κ r`, `E₁ = ℕ →ᵇ K₁`, `B` = the library's
  `ProjectiveExteriorCompletion K₁ ℕ k`, `W_B` = the library's `completedExteriorWedge K₁ ℕ k`
  (definitions only; see challenges `ThmC_1` and `LemC_2`).
* `c₀(ℕ, K₁)` is Mathlib's `C₀(ℕ, K₁)` (`ZeroAtInftyContinuousMap` on discrete `ℕ`, sup norm), and
  the inclusion `c₀ ⊆ E₁` is `ZeroAtInftyContinuousMap.toBCF` (an isometry).
* `D_a` is `ContinuousLinearMap.mul K₁ (ℕ →ᵇ K₁) a` (coordinatewise multiplication).
* `σ` is `sigma` (introduced here). A bounded `k`-linear lift of `σ` is a continuous `k`-linear map
  `p : c₀(ℕ, K₁)^k → Alt^k(E₁; B)` with `p(a, …, a) = σ(a)`.
* `A(u)` is `ContinuousAlternatingMap.compContinuousLinearMapCLM u` on `Alt^k(E₁; B)`.
* Status: not formalized in the library (no declaration about lifts over a `c₀` base).
* Universe: `κ : Type u`.
* `set_option backward.isDefEq.respectTransparency false` (as in the library) is needed for
  instance search on `ℕ →ᵇ K₁`; it does not change any statement.
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
  sorry

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
  sorry

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
  sorry

end AlternatingAnalyticChallenge.PropC_6
