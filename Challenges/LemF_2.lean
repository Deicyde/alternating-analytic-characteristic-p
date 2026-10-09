import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import AlternatingAnalytic.Analysis.SphericalCompleteness

/-!
# Lemma F.2 (multilinear tails), pp. 51-52

Paper statement: "Let K be complete, nonarchimedean and not spherically complete, let I be
countably infinite, and let d ≥ 1. Every bounded d-linear map λ : ℓ^∞(I, K)^d → K has an
expansion
  λ(x^1, …, x^d) = Σ_{(i_1, …, i_d) ∈ I^d} a_{i_1,…,i_d} x^1_{i_1} ⋯ x^d_{i_d},
  a_{i_1,…,i_d} = λ(e_{i_1}, …, e_{i_d}),                                         (F.1)
where a ∈ c_0(I^d, K). Consequently, for every ε > 0, there is a finite S ⊆ I such that
|λ(x^1, …, x^d)| ≤ ε whenever all ‖x^r‖ ≤ 1 and at least one x^r vanishes on S. In particular
λ(e_i, …, e_i) → 0 outside finite subsets of I."

The sum in (F.1) is unconditional: over a complete nonarchimedean field every null family is
unconditionally summable.

## Formalization notes

* `K` is a `NontriviallyNormedField` with `[CompleteSpace K]`, `[IsUltrametricDist K]` and
  `¬ SphericallyCompleteSpace K`. Nontriviality is no restriction, since a trivially normed field
  is spherically complete. `SphericallyCompleteSpace` is the library class, imported for this
  definition only.
* `I` has `[Countable I]`, `[Infinite I]` and `[DecidableEq I]` (needed by `lp.single`). The unit
  vector `e_i` is `lp.single ∞ i 1`.
* `ℓ^∞(I, K)` is `lp (fun _ : I => K) ∞`; `I^d` is `Fin d → I`.
* The paper's `λ` is called `μ`, since `λ` is reserved in Lean. It is a
  `ContinuousMultilinearMap K (fun _ : Fin d => ℓ^∞(I, K)) K`.
* Part 1: `a ∈ c_0(I^d, K)` is `Tendsto a cofinite (𝓝 0)`, and the expansion is a `HasSum` over
  `Fin d → I`.
* Part 2 is the tail property, with `S : Finset I` and "`x^r` vanishes on `S`" as
  `∀ i ∈ S, x r i = 0`. Part 3 is `λ(e_i, …, e_i) → 0` along the cofinite filter.
-/

open Filter Topology
open scoped ENNReal

namespace AlternatingAnalyticChallenge.LemF_2

universe u v

/-- Lemma F.2, part 1: the coefficients `a_i = λ(e_{i_1}, …, e_{i_d})` tend to zero on `I^d`, and
`λ(x^1, …, x^d)` is the unconditional sum of `a_i x^1_{i_1} ⋯ x^d_{i_d}` (F.1). -/
theorem multilinear_expansion
    {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    (hK : ¬ SphericallyCompleteSpace K)
    {I : Type v} [Countable I] [Infinite I] [DecidableEq I] {d : ℕ} (hd : 1 ≤ d)
    (μ : ContinuousMultilinearMap K (fun _ : Fin d => lp (fun _ : I => K) ∞) K) :
    Tendsto (fun i : Fin d → I => μ (fun r => lp.single ∞ (i r) (1 : K))) cofinite (𝓝 0) ∧
      ∀ x : Fin d → lp (fun _ : I => K) ∞,
        HasSum
          (fun i : Fin d → I =>
            μ (fun r => lp.single ∞ (i r) (1 : K)) * ∏ r, (x r : I → K) (i r))
          (μ x) := by
  sorry

/-- Lemma F.2, part 2: for every `ε > 0` there is a finite `S ⊆ I` such that
`|λ(x^1, …, x^d)| ≤ ε` whenever all `‖x^r‖ ≤ 1` and some `x^r` vanishes on `S`. -/
theorem multilinear_tail
    {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    (hK : ¬ SphericallyCompleteSpace K)
    {I : Type v} [Countable I] [Infinite I] [DecidableEq I] {d : ℕ} (hd : 1 ≤ d)
    (μ : ContinuousMultilinearMap K (fun _ : Fin d => lp (fun _ : I => K) ∞) K)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ S : Finset I, ∀ x : Fin d → lp (fun _ : I => K) ∞, (∀ r, ‖x r‖ ≤ 1) →
      (∃ r, ∀ i ∈ S, (x r : I → K) i = 0) → ‖μ x‖ ≤ ε := by
  sorry

/-- Lemma F.2, part 3: `λ(e_i, …, e_i)` tends to `0` outside finite subsets of `I`. -/
theorem multilinear_diagonal_tendsto_zero
    {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    (hK : ¬ SphericallyCompleteSpace K)
    {I : Type v} [Countable I] [Infinite I] [DecidableEq I] {d : ℕ} (hd : 1 ≤ d)
    (μ : ContinuousMultilinearMap K (fun _ : Fin d => lp (fun _ : I => K) ∞) K) :
    Tendsto (fun i : I => μ (fun _ => lp.single ∞ i (1 : K))) cofinite (𝓝 0) := by
  sorry

end AlternatingAnalyticChallenge.LemF_2
