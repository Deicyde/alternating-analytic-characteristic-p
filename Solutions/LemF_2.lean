import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import AlternatingAnalytic.Analysis.SphericalCompleteness
import AlternatingAnalytic.Scalar.Tails.Expansion

/-!
# Proof of Lemma F.2

Uses `Tails.multilinear_expansion`, `Tails.multilinear_tail` and
`Tails.multilinear_diagonal_tendsto_zero` from `AlternatingAnalytic/Scalar/Tails/`.
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
          (μ x) :=
  AlternatingAnalytic.Tails.multilinear_expansion hK μ

/-- Lemma F.2, part 2: for every `ε > 0` there is a finite `S ⊆ I` such that
`|λ(x^1, …, x^d)| ≤ ε` whenever all `‖x^r‖ ≤ 1` and some `x^r` vanishes on `S`. -/
theorem multilinear_tail
    {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    (hK : ¬ SphericallyCompleteSpace K)
    {I : Type v} [Countable I] [Infinite I] [DecidableEq I] {d : ℕ} (hd : 1 ≤ d)
    (μ : ContinuousMultilinearMap K (fun _ : Fin d => lp (fun _ : I => K) ∞) K)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ S : Finset I, ∀ x : Fin d → lp (fun _ : I => K) ∞, (∀ r, ‖x r‖ ≤ 1) →
      (∃ r, ∀ i ∈ S, (x r : I → K) i = 0) → ‖μ x‖ ≤ ε :=
  AlternatingAnalytic.Tails.multilinear_tail hK μ ε hε

/-- Lemma F.2, part 3: `λ(e_i, …, e_i)` tends to `0` outside finite subsets of `I`. -/
theorem multilinear_diagonal_tendsto_zero
    {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    (hK : ¬ SphericallyCompleteSpace K)
    {I : Type v} [Countable I] [Infinite I] [DecidableEq I] {d : ℕ} (hd : 1 ≤ d)
    (μ : ContinuousMultilinearMap K (fun _ : Fin d => lp (fun _ : I => K) ∞) K) :
    Tendsto (fun i : I => μ (fun _ => lp.single ∞ i (1 : K))) cofinite (𝓝 0) :=
  AlternatingAnalytic.Tails.multilinear_diagonal_tendsto_zero hK hd μ

end AlternatingAnalyticChallenge.LemF_2
