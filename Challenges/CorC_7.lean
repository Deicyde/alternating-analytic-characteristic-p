import AlternatingAnalytic.Analysis.LaurentField
import AlternatingAnalytic.Analysis.ProjectiveExterior
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-!
# Corollary C.7 (diagonal transitions over a `c₀` base), pp. 40-41

Paper statement (Appendix C, §C.6, `Corollary C.7`; `κ`, `k`, `r`, `K₁`, `E₁`, `B`, `W_B` as in
Theorem C.1: `κ` a finite field of characteristic `p`, `k ≥ p`, `r ∈ (0, 1)`, `K₁ = κ((X))`,
`E₁ = ℓ^∞(ℕ, K₁)`, `B` the projective exterior completion, `W_B(x) = x₁ ∧ ⋯ ∧ x_k`; `D_a` is
multiplication by `a`): Let `U` be the open unit ball of `c₀(ℕ, K₁)`, an analytic manifold with one
chart. Let `𝒱 → U` be the trivial bundle with fiber `E₁` and the two global trivializations
`τ₀(a, z) = (a, z)` and `τ₁(a, z) = (a, D_{1+a} z)`, and let `ℬ = U × B`. Then `𝒱` is an analytic
normed vector bundle whose transitions are isometric diagonal automorphisms of `E₁`. The naturally
induced atlas on `Alt^k(𝒱; ℬ)` is not analytic: the section that is constantly `W_B` in the chart
induced by `τ₁` is, in the chart induced by `τ₀`, the map `a ↦ W_B ∘ (D_{1+a}, …, D_{1+a})`, which
is analytic at no point of `U`.

## Formalization notes
* Choice of formulation: the explicit-map form, not a `ContMDiffVectorBundle` statement. The
  bundle `𝒱` and its two-chart atlas are encoded by the transition `a ↦ D_{1+a}` on
  `U = Metric.ball 0 1 ⊆ c₀(ℕ, K₁)`. Part 1 says the transitions are isometric (`‖D_{1+a} z‖ = ‖z‖`),
  invertible, diagonal (they are multiplication operators by definition), and that the transition
  and its inverse are analytic on `U` (so `𝒱` with the atlas `{τ₀, τ₁}` is an analytic normed vector
  bundle). Part 2 says the chart-`τ₀` expression `a ↦ W_B ∘ (D_{1+a}, …, D_{1+a})` of the section
  constantly `W_B` in chart `τ₁` is analytic at no point of `U`. The identification of this map with
  the chart expression of the induced atlas on `Alt^k(𝒱; ℬ)` (the transition of the induced atlas
  being `m ↦ m ∘ (D_{1+a}, …, D_{1+a})`) is not itself formalized.
* Degree: index type `Fin k`. Finite field of characteristic `p`: `[Finite κ]`, `p.Prime`,
  `[CharP κ p]`; the hypotheses of the subsection apply to both parts.
* `K₁ = AlternatingAnalytic.LaurentField κ r`, `E₁ = ℕ →ᵇ K₁`, `B` = library
  `ProjectiveExteriorCompletion K₁ ℕ k`, `W_B` = library `completedExteriorWedge K₁ ℕ k`
  (definitions only). `c₀(ℕ, K₁) = C₀(ℕ, K₁)` with inclusion `ZeroAtInftyContinuousMap.toBCF`;
  `1 + a` is computed in `E₁ = ℕ →ᵇ K₁`, and `D_b = ContinuousLinearMap.mul K₁ (ℕ →ᵇ K₁) b`.
* The inverse transition is `Ring.inverse (D_{1+a})` in the Banach algebra `L(E₁, E₁)`.
* Status: not formalized in the library. Part 2 is the `u₀ = id` instance of `PropC_6`'s
  `part2_not_analyticAt_apply_wedge` (`id + D_a = D_{1+a}`), restricted to `U`.
* Universe: `κ : Type u`.
* `set_option backward.isDefEq.respectTransparency false` (as in the library) is needed for
  instance search on `ℕ →ᵇ K₁`; it does not change any statement.
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

/-- **Corollary C.7, part 1.** On the open unit ball `U` of `c₀(ℕ, K₁)` the transitions
`D_{1+a}` are isometric diagonal automorphisms of `E₁`, and the transition and its inverse are
analytic on `U`. -/
theorem part1_analytic_isometric_transitions
    (κ : Type u) [Field κ] [Finite κ] (p : ℕ) (hp : p.Prime) [CharP κ p]
    (k : ℕ) (hpk : p ≤ k) (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] :
    (∀ a ∈ Metric.ball (0 : C₀(ℕ, LaurentField κ r)) 1, ∀ z : ℕ →ᵇ LaurentField κ r,
      ‖transition κ r a z‖ = ‖z‖) ∧
    (∀ a ∈ Metric.ball (0 : C₀(ℕ, LaurentField κ r)) 1, IsUnit (transition κ r a)) ∧
    AnalyticOnNhd (LaurentField κ r) (transition κ r)
      (Metric.ball (0 : C₀(ℕ, LaurentField κ r)) 1) ∧
    AnalyticOnNhd (LaurentField κ r) (fun a => Ring.inverse (transition κ r a))
      (Metric.ball (0 : C₀(ℕ, LaurentField κ r)) 1) := by
  sorry

/-- **Corollary C.7, part 2.** The section constantly `W_B` in the chart induced by `τ₁` reads
`a ↦ W_B ∘ (D_{1+a}, …, D_{1+a})` in the chart induced by `τ₀`, and this map is analytic at no point
of `U`. -/
theorem part2_not_analyticAt
    (κ : Type u) [Field κ] [Finite κ] (p : ℕ) (hp : p.Prime) [CharP κ p]
    (k : ℕ) (hpk : p ≤ k) (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] :
    ∀ a₀ ∈ Metric.ball (0 : C₀(ℕ, LaurentField κ r)) 1,
      ¬ AnalyticAt (LaurentField κ r)
        (fun a : C₀(ℕ, LaurentField κ r) =>
          (completedExteriorWedge (LaurentField κ r) ℕ k).compContinuousLinearMap
            (transition κ r a)) a₀ := by
  sorry

end AlternatingAnalyticChallenge.CorC_7
