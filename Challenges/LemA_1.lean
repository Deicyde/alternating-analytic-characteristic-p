import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Lemma A.1 (one-variable uniqueness), p. 25

Paper statement: "Let K be nontrivially normed and Z a normed K-space, not necessarily
complete. Let z₀, z₁, … ∈ Z, ρ > 0 and M ≥ 0 with ‖zₙ‖ρⁿ ≤ M for all n. If ∑ₙ tⁿ zₙ
converges to 0 for every t ∈ K with |t| < ρ, then zₙ = 0 for all n."

Formalization notes:
* No completeness of `K` or `Z` is assumed, as in the paper.
* "∑ₙ tⁿ zₙ converges to 0" is read as convergence of the ordered partial sums
  `∑_{n<N} tⁿ • zₙ → 0` (`Filter.Tendsto` along `atTop`), not as unconditional summation
  (`HasSum`). Under the bound `‖zₙ‖ρⁿ ≤ M` the two readings agree, but the partial-sum
  reading is the literal one.
* The hypothesis `M ≥ 0` is kept although it follows from the bound at `n = 0`.
* No definitions are introduced.
-/

open Filter Topology

namespace AlternatingAnalyticChallenge.LemA_1

/-- **Lemma A.1.** If `‖z n‖ ρ ^ n ≤ M` for all `n` and the partial sums of `∑ tⁿ z n` tend
to `0` for every `t` with `‖t‖ < ρ`, then every `z n` is zero. `Z` need not be complete. -/
theorem one_variable_uniqueness
    (K : Type*) [NontriviallyNormedField K]
    (Z : Type*) [NormedAddCommGroup Z] [NormedSpace K Z]
    (z : ℕ → Z) (ρ M : ℝ) (hρ : 0 < ρ) (hM : 0 ≤ M)
    (hbound : ∀ n, ‖z n‖ * ρ ^ n ≤ M)
    (hconv : ∀ t : K, ‖t‖ < ρ →
      Tendsto (fun N => ∑ n ∈ Finset.range N, t ^ n • z n) atTop (𝓝 0)) :
    ∀ n, z n = 0 := by
  sorry

end AlternatingAnalyticChallenge.LemA_1
