import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import AlternatingAnalytic.Analysis.SphericalCompleteness

/-!
# Lemma F.2 (multilinear tails), pp. 49-50

Paper statement: "Let K be complete, nonarchimedean and not spherically complete, let I be
countably infinite, and let d ≥ 1. Every bounded d-linear map λ : ℓ^∞(I, K)^d → K has an
expansion
  λ(x^1, …, x^d) = Σ_{(i_1, …, i_d) ∈ I^d} a_{i_1,…,i_d} x^1_{i_1} ⋯ x^d_{i_d},
  a_{i_1,…,i_d} = λ(e_{i_1}, …, e_{i_d}),                                         (F.1)
where a ∈ c_0(I^d, K). Consequently, for every ε > 0, there is a finite S ⊆ I such that
|λ(x^1, …, x^d)| ≤ ε whenever all ‖x^r‖ ≤ 1 and at least one x^r vanishes on S. In particular
λ(e_i, …, e_i) → 0 outside finite subsets of I."

The sum in (F.1) is an unconditional sum of a null family over a complete nonarchimedean field
(paper, §F.1: "every null scalar family is unconditionally summable").

## Formalization notes
* `K` is a `NontriviallyNormedField` with `[CompleteSpace K]`, `[IsUltrametricDist K]` and
  `¬ SphericallyCompleteSpace K`. Nontriviality of the norm is not a restriction: a trivially
  normed field is spherically complete (its nontrivial closed balls are points or the whole field).
  `SphericallyCompleteSpace` is the library class (every nonempty family of pairwise-meeting closed
  balls has a common point) from `AlternatingAnalytic.Analysis.SphericalCompleteness`, imported for
  this definition only; that module proves only positive extension results.
* `I` is a type with `[Countable I]` and `[Infinite I]`; `[DecidableEq I]` is added because
  Mathlib's `lp.single` (the coordinate vector `e_i = lp.single ∞ i 1`) needs it.
* `ℓ^∞(I, K)` is Mathlib's `lp (fun _ : I => K) ∞` with the sup norm; `I^d` is `Fin d → I`.
* The paper's `λ` is called `μ` (`λ` is reserved syntax in Lean).
* "Bounded d-linear" is `ContinuousMultilinearMap K (fun _ : Fin d => ℓ^∞(I, K)) K` (bounded and
  continuous agree over a nontrivially normed field).
* `a ∈ c_0(I^d, K)` is `Tendsto a cofinite (𝓝 0)`; the expansion is `HasSum` over `Fin d → I`
  (unconditional summation along finite subsets, as in the paper). These two together are part 1.
* Part 2 is the tail property: `S` is a `Finset I`; "x^r vanishes on S" is
  `∀ i ∈ S, x r i = 0`. Part 3 is `λ(e_i, …, e_i) → 0` along the cofinite filter of `I`.
* No definitions are introduced. Not formalized in this library: there is no proof to compare
  against. `THEOREM_MAP-HEAD.md` reports that the tail input was checked separately outside
  this repository; that check was not inspected here.
-/

open Filter Topology
open scoped ENNReal

namespace AlternatingAnalyticChallenge.LemF_2

universe u v

/-- **Lemma F.2, part 1 (null coefficient array and expansion (F.1)).** The coefficient array
`a_i = λ(e_{i_1}, …, e_{i_d})` is null on `I^d`, and `λ(x^1, …, x^d)` is the unconditional sum of
`a_i x^1_{i_1} ⋯ x^d_{i_d}` over `i ∈ I^d`. -/
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

/-- **Lemma F.2, part 2 (tail property).** For every `ε > 0` there is a finite `S ⊆ I` such that
`|λ(x^1, …, x^d)| ≤ ε` whenever all `‖x^r‖ ≤ 1` and at least one `x^r` vanishes on `S`. -/
theorem multilinear_tail
    {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    (hK : ¬ SphericallyCompleteSpace K)
    {I : Type v} [Countable I] [Infinite I] [DecidableEq I] {d : ℕ} (hd : 1 ≤ d)
    (μ : ContinuousMultilinearMap K (fun _ : Fin d => lp (fun _ : I => K) ∞) K)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ S : Finset I, ∀ x : Fin d → lp (fun _ : I => K) ∞, (∀ r, ‖x r‖ ≤ 1) →
      (∃ r, ∀ i ∈ S, (x r : I → K) i = 0) → ‖μ x‖ ≤ ε := by
  sorry

/-- **Lemma F.2, part 3.** The diagonal values `λ(e_i, …, e_i)` tend to `0` outside finite subsets
of `I`. -/
theorem multilinear_diagonal_tendsto_zero
    {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    (hK : ¬ SphericallyCompleteSpace K)
    {I : Type v} [Countable I] [Infinite I] [DecidableEq I] {d : ℕ} (hd : 1 ≤ d)
    (μ : ContinuousMultilinearMap K (fun _ : Fin d => lp (fun _ : I => K) ∞) K) :
    Tendsto (fun i : I => μ (fun _ => lp.single ∞ i (1 : K))) cofinite (𝓝 0) := by
  sorry

end AlternatingAnalyticChallenge.LemF_2
