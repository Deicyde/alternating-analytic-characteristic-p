import AlternatingAnalytic.Analysis.LaurentField
import AlternatingAnalytic.Analysis.ProjectiveExterior
import AlternatingAnalytic.Analysis.EquivalentUltrametric
import AlternatingAnalytic.Analysis.CompletedBaseChange
import Mathlib.Analysis.Analytic.Basic

/-!
# Remark E.2 (the case `K₁ = K̂`; direct `F_q((u))` route), p. 50

Paper statement (Appendix E, after the proof of Theorem 6.1(1)). "If `K₁ = K̂`, as when
`K = F_p((u))` and `t = u`, the completed tensor products identify isometrically with `E₁` and
`B`: use Lemma D.6(3) and `x ⊗ λ = λx ⊗ 1`. Thus `E` is nonarchimedean in this case. For
`K = F_q((u))`, `q = p^n`, with its `u`-adic absolute value, one can instead apply Theorem C.1
directly with `κ = F_q` and `X = u`, obtaining `E = ℓ^∞(ℕ, K)` and `F = B`. The proof over a
general base field does not require, or assert, that `E` is nonarchimedean."

In the proof of Theorem 6.1(1), `E = E₁ ⊗̂_π K̂` and `F = B ⊗̂_π K̂` with `E₁ = ℓ^∞(ℕ, K₁)`;
Theorem 6.1(1) asserts that `A^k_{E,E;F}` is analytic at no point and that `F` admits no
equivalent nonarchimedean norm (for `k ≥ p`).

## Formalization notes

* Part 1 (`K₁ = K'`, where the paper's `K̂` plays the role of the field `K'` of Appendix D): `K`
  satisfies (H1) and (H2) and serves as both `K₁` and `K'` (`NormedAlgebra.id`). The statement is for every complete normed `K`-space `V`, not only
  `V = E₁` and `V = B`; the paper's argument works in that generality. The conclusion is that the
  isometry `completedBaseChangeEmbedding K V K : V → V ⊗̂_π K` is surjective.
* Part 2: in this case `E = ℓ^∞(ℕ, K₁) ⊗̂_π K₁` is nonarchimedean.
* Part 3: `F_q((u))` with its `u`-adic absolute value is `LaurentField κ r` with `κ` finite of
  characteristic `p` and `r ∈ (0, 1)`; `E = ℕ →ᵇ K` and `F = B = ProjectiveExteriorCompletion K ℕ k`.
  The conclusion is Theorem 6.1(1) for these spaces and `k ≥ p`: `A^k`
  (`compContinuousLinearMapCLM`, index `Fin k`) is analytic at no point, and `B` admits no
  equivalent nonarchimedean norm (`HasEquivalentUltrametricNorm`).
* The last sentence of the remark makes no claim and is not formalized.
* `set_option backward.isDefEq.respectTransparency false` lets instance search find the
  `LaurentField κ r`-module structure on `ℕ →ᵇ LaurentField κ r`.
-/

set_option backward.isDefEq.respectTransparency false

open scoped NNReal BoundedContinuousFunction

namespace AlternatingAnalyticChallenge.RemE_2

open AlternatingAnalytic

universe u

/-- Remark E.2, part 1: when `K₁ = K'`, the canonical isometry `V → V ⊗̂_π K` is surjective for
every Banach space `V`. -/
theorem completedBaseChangeEmbedding_surjective_self
    (K V : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    [SphericallyCompleteSpace K] [NormedAddCommGroup V] [NormedSpace K V] [CompleteSpace V] :
    Function.Surjective (completedBaseChangeEmbedding K V K) := by
  sorry

/-- Remark E.2, part 2: when `K₁ = K'`, the source `E = ℓ^∞(ℕ, K₁) ⊗̂_π K₁` is nonarchimedean. -/
theorem isUltrametricDist_completedBaseChange_self
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    [SphericallyCompleteSpace K] :
    IsUltrametricDist (CompletedBaseChange K (ℕ →ᵇ K) K) := by
  sorry

/-- Remark E.2, part 3: over `K = F_q((u))`, Theorem 6.1(1) holds with `E = ℓ^∞(ℕ, K)` and
`F = B` for every `k ≥ p`. -/
theorem laurent_direct_counterexample
    (κ : Type u) [Field κ] [Finite κ] (p : ℕ) (hp : p.Prime) [CharP κ p]
    (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] (k : ℕ) (hpk : p ≤ k) :
    (∀ f₀ : (ℕ →ᵇ LaurentField κ r) →L[LaurentField κ r] (ℕ →ᵇ LaurentField κ r),
      ¬ AnalyticAt (LaurentField κ r)
        (fun f : (ℕ →ᵇ LaurentField κ r) →L[LaurentField κ r] (ℕ →ᵇ LaurentField κ r) =>
          (ContinuousAlternatingMap.compContinuousLinearMapCLM f :
            ((ℕ →ᵇ LaurentField κ r) [⋀^Fin k]→L[LaurentField κ r]
                ProjectiveExteriorCompletion (LaurentField κ r) ℕ k) →L[LaurentField κ r]
              ((ℕ →ᵇ LaurentField κ r) [⋀^Fin k]→L[LaurentField κ r]
                ProjectiveExteriorCompletion (LaurentField κ r) ℕ k))) f₀) ∧
      ¬ HasEquivalentUltrametricNorm (LaurentField κ r)
        (ProjectiveExteriorCompletion (LaurentField κ r) ℕ k) := by
  sorry

end AlternatingAnalyticChallenge.RemE_2
