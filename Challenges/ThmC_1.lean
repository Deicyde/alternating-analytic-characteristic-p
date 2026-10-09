import AlternatingAnalytic.Analysis.LaurentField
import AlternatingAnalytic.Analysis.ProjectiveExterior

/-!
# Theorem C.1 (no bounded lift over a Laurent series field), p. 37

Paper statement (Appendix C, `Theorem C.1`): Let `κ` be a finite field of characteristic `p`,
let `k ≥ p` and `r ∈ (0, 1)`, and let `K₁ = κ((X))` with `|X| = r`. Let `E₁ = ℓ^∞(ℕ, K₁)`, and
let `B` be the completion of `Λ^k_{K₁} E₁` under the projective exterior norm. Then
`A^{k,K₁}_{E₁,E₁;B}` admits no bounded `k`-linear lift over `K₁`. Consequently it is analytic at
no point of `L(E₁, E₁)`.

Here `A^{k,K}_{E,E';F} : L(E,E') → L(Alt^k(E';F), Alt^k(E;F))`, `A(f)(m) = m ∘ (f, …, f)`, and a
bounded `k`-linear lift is a bounded `k`-linear map on `L(E,E')^k` whose diagonal is `A`.

## Formalization notes
* The degree index type is `Fin k`.
* `K₁ = κ((X))` with `|a| = r^{ord a}` is the library's `LaurentField κ r`, a type synonym for
  `LaurentSeries κ`; `0 < r < 1` is given by `Fact` instances.
* `E₁ = ℓ^∞(ℕ, K₁)` is `ℕ →ᵇ K₁` with the sup norm.
* `B` is the library's `ProjectiveExteriorCompletion K₁ ℕ k`: the completion of
  `⋀[K₁]^k (ℕ →ᵇ K₁)` under `‖ω‖_π = inf ∑_j ∏_i ‖x_{j,i}‖` (see Lemma C.2).
* "Finite field of characteristic `p`" is `[Finite κ]`, `p.Prime`, `[CharP κ p]`.
* `HasBoundedKLinearLift` is the paper's bounded `k`-linear lift.
* "Analytic at no point" is `¬ AnalyticAt K₁ A f₀` for every `f₀ : E₁ →L[K₁] E₁`.
* `set_option backward.isDefEq.respectTransparency false` is needed to find the `K₁`-module
  structure on `ℕ →ᵇ K₁`; it does not change any statement.
-/

set_option backward.isDefEq.respectTransparency false

open scoped NNReal BoundedContinuousFunction

namespace AlternatingAnalyticChallenge.ThmC_1

open AlternatingAnalytic

universe u

/-- Precomposition `A : f ↦ (m ↦ m ∘ (f, …, f))` on `Alt^k(E; F)` has a bounded `k`-linear lift:
a continuous `k`-linear map on `L(E,E)` whose diagonal is `A`. -/
def HasBoundedKLinearLift (K : Type*) [NontriviallyNormedField K]
    (E F : Type*) [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup F] [NormedSpace K F] (k : ℕ) : Prop :=
  ∃ P : ContinuousMultilinearMap K (fun _ : Fin k => E →L[K] E)
      ((E [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F)),
    ∀ f : E →L[K] E, P (fun _ => f) = ContinuousAlternatingMap.compContinuousLinearMapCLM f

/-- Over `K₁ = κ((X))` with `κ` finite of characteristic `p ≤ k`, precomposition on
`Alt^k(ℓ^∞(ℕ,K₁); B)` has no bounded `k`-linear lift. -/
theorem part1_not_hasBoundedKLinearLift
    (κ : Type u) [Field κ] [Finite κ] (p : ℕ) (hp : p.Prime) [CharP κ p]
    (k : ℕ) (hpk : p ≤ k) (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] :
    ¬ HasBoundedKLinearLift (LaurentField κ r) (ℕ →ᵇ LaurentField κ r)
      (ProjectiveExteriorCompletion (LaurentField κ r) ℕ k) k := by
  sorry

/-- The same precomposition map is analytic at no point of `L(E₁, E₁)`. -/
theorem part2_not_analyticAt
    (κ : Type u) [Field κ] [Finite κ] (p : ℕ) (hp : p.Prime) [CharP κ p]
    (k : ℕ) (hpk : p ≤ k) (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)]
    (f₀ : (ℕ →ᵇ LaurentField κ r) →L[LaurentField κ r] (ℕ →ᵇ LaurentField κ r)) :
    ¬ AnalyticAt (LaurentField κ r)
      (fun f : (ℕ →ᵇ LaurentField κ r) →L[LaurentField κ r] (ℕ →ᵇ LaurentField κ r) =>
        (ContinuousAlternatingMap.compContinuousLinearMapCLM f :
          ((ℕ →ᵇ LaurentField κ r) [⋀^Fin k]→L[LaurentField κ r]
              ProjectiveExteriorCompletion (LaurentField κ r) ℕ k) →L[LaurentField κ r]
            ((ℕ →ᵇ LaurentField κ r) [⋀^Fin k]→L[LaurentField κ r]
              ProjectiveExteriorCompletion (LaurentField κ r) ℕ k))) f₀ := by
  sorry

end AlternatingAnalyticChallenge.ThmC_1
