import AlternatingAnalytic.Laurent.FiniteDimSharp.TrivialBundleAction
import AlternatingAnalytic.Laurent.FiniteDimSharp.MultiplierFamily
import AlternatingAnalytic.Laurent.FiniteDimSharp.Obstruction

/-!
# Infinite-dimensional nonarchimedean model spaces do not preserve analytic morphisms

The "only if" half of Corollary C.8. Over a complete discretely valued ultrametric field `K`, if
`a ↦ A(u₀ + D_a)` is analytic at no point of `c₀(ℕ, K)` for a target `B`, then preservation of
analytic morphisms over `P` (with an equivalent ultrametric norm) forces `dim P < ∞`:
`exists_not_analyticAt_of_not_finiteDimensional` gives a continuous linear family `U` with
`x ↦ A(U x)` not analytic somewhere, while `analyticAt_compContinuousLinearMapCLM_of_preserves`
makes it analytic everywhere. For `K = κ((X))` the hypothesis is Proposition C.6
(`CZeroOperatorObstruction`).
-/

set_option backward.isDefEq.respectTransparency false

open scoped NNReal BoundedContinuousFunction ZeroAtInfty

namespace AlternatingAnalytic.FiniteDimSharp

universe u

/-- Over a complete discretely valued ultrametric field, the `c₀` multiplier obstruction for a
target `B` forces every model space preserving analytic morphisms to be finite-dimensional. -/
theorem finiteDimensional_of_preservesAnalyticMorphisms_of_discrete {K : Type u}
    [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] {e : ℝ} (he : 1 < e)
    (hval : ∀ c : K, c ≠ 0 → ∃ n : ℤ, ‖c‖ = e ^ n) (hK : ∀ n : ℤ, ∃ c : K, ‖c‖ = e ^ n)
    (B : Type u) [NormedAddCommGroup B] [NormedSpace K B] (k : ℕ)
    (hC6 : ∀ (u₀ : (ℕ →ᵇ K) →L[K] (ℕ →ᵇ K)) (a₀ : C₀(ℕ, K)),
      ¬ AnalyticAt K (fun a : C₀(ℕ, K) =>
        (ContinuousAlternatingMap.compContinuousLinearMapCLM
          (u₀ + ContinuousLinearMap.mul K (ℕ →ᵇ K) a.toBCF) :
          ((ℕ →ᵇ K) [⋀^Fin k]→L[K] B) →L[K] ((ℕ →ᵇ K) [⋀^Fin k]→L[K] B))) a₀)
    (P : Type u) [NormedAddCommGroup P] [NormedSpace K P] [CompleteSpace P]
    (hP : HasEquivalentUltrametricNorm K P) (h : PreservesAnalyticMorphisms K P k) :
    FiniteDimensional K P := by
  by_contra hinf
  obtain ⟨U, x₀, hU⟩ :=
    exists_not_analyticAt_of_not_finiteDimensional he hval hK B k hC6 P hP hinf
  exact hU (analyticAt_compContinuousLinearMapCLM_of_preserves (ℕ →ᵇ K) B h U x₀)

/-- Corollary C.8, "only if" half, assuming Proposition C.6: over `K = κ((X))`, if the
alternating construction preserves operator-valued analytic morphisms over every analytic
manifold modeled on the Banach space `P` (with an equivalent ultrametric norm), then `P` is
finite-dimensional. -/
theorem finiteDimensional_of_preservesAnalyticMorphisms
    (κ : Type u) [Field κ] (k : ℕ) (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)]
    (hC6 : CZeroOperatorObstruction κ r k)
    (P : Type u) [NormedAddCommGroup P] [NormedSpace (LaurentField κ r) P] [CompleteSpace P]
    (hP : HasEquivalentUltrametricNorm (LaurentField κ r) P)
    (h : PreservesAnalyticMorphisms (LaurentField κ r) P k) :
    FiniteDimensional (LaurentField κ r) P :=
  finiteDimensional_of_preservesAnalyticMorphisms_of_discrete (one_lt_inv_radius r)
    (laurent_norm_mem_zpowers κ r) (laurent_exists_norm_eq_zpow κ r)
    (ProjectiveExteriorCompletion (LaurentField κ r) ℕ k) k hC6 P hP h

/-- Corollary C.8, "only if" half: over `K = 𝔽_q((u))` with `k ≥ p`, if the alternating
construction preserves analytic bundles and operator-valued analytic morphisms over every analytic
manifold modeled on the Banach space `P` (with an equivalent ultrametric norm), then `P` is
finite-dimensional. Only morphism preservation is used. -/
theorem finiteDimensional_of_preserves
    (κ : Type u) [Field κ] [Finite κ] (p : ℕ) (hp : p.Prime) [CharP κ p]
    (k : ℕ) (hpk : p ≤ k) (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)]
    (P : Type u) [NormedAddCommGroup P] [NormedSpace (LaurentField κ r) P] [CompleteSpace P]
    (hP : HasEquivalentUltrametricNorm (LaurentField κ r) P)
    (h : PreservesAnalyticBundles (LaurentField κ r) P k ∧
      PreservesAnalyticMorphisms (LaurentField κ r) P k) :
    FiniteDimensional (LaurentField κ r) P :=
  finiteDimensional_of_preservesAnalyticMorphisms κ k r
    (cZeroOperatorObstruction_of_charP κ p hp k hpk r) P hP h.2

end AlternatingAnalytic.FiniteDimSharp
