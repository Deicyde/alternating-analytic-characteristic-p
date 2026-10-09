import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import AlternatingAnalytic.Analysis.SphericalCompleteness
import AlternatingAnalytic.Scalar.Tails.Expansion

/-!
# Lemma F.2 (multilinear tails), pp. 49-50

Solution: the three statements of `Challenges/LemF_2.lean`, proved from the library
(`AlternatingAnalytic/Scalar/Tails/`):
* part 1: `AlternatingAnalytic.Tails.multilinear_expansion` (`Expansion.lean`): the null array is
  `multilinear_coeff_tendsto_zero` and the expansion is `multilinear_hasSum` (`LpTails.lean`,
  `Expansion.lean`);
* part 2: `AlternatingAnalytic.Tails.multilinear_tail` (`LpTails.lean`), transported along an
  enumeration of `I` from `tail_multilinear` on `ℓ^∞(ℕ)` (`Multilinear.lean`) under `NSC`, which
  follows from the failure of spherical completeness (`NestedBalls.lean`);
* part 3: `AlternatingAnalytic.Tails.multilinear_diagonal_tendsto_zero` (`LpTails.lean`).
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
          (μ x) :=
  AlternatingAnalytic.Tails.multilinear_expansion hK μ

/-- **Lemma F.2, part 2 (tail property).** For every `ε > 0` there is a finite `S ⊆ I` such that
`|λ(x^1, …, x^d)| ≤ ε` whenever all `‖x^r‖ ≤ 1` and at least one `x^r` vanishes on `S`. -/
theorem multilinear_tail
    {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    (hK : ¬ SphericallyCompleteSpace K)
    {I : Type v} [Countable I] [Infinite I] [DecidableEq I] {d : ℕ} (hd : 1 ≤ d)
    (μ : ContinuousMultilinearMap K (fun _ : Fin d => lp (fun _ : I => K) ∞) K)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ S : Finset I, ∀ x : Fin d → lp (fun _ : I => K) ∞, (∀ r, ‖x r‖ ≤ 1) →
      (∃ r, ∀ i ∈ S, (x r : I → K) i = 0) → ‖μ x‖ ≤ ε :=
  AlternatingAnalytic.Tails.multilinear_tail hK μ ε hε

/-- **Lemma F.2, part 3.** The diagonal values `λ(e_i, …, e_i)` tend to `0` outside finite subsets
of `I`. -/
theorem multilinear_diagonal_tendsto_zero
    {K : Type u} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    (hK : ¬ SphericallyCompleteSpace K)
    {I : Type v} [Countable I] [Infinite I] [DecidableEq I] {d : ℕ} (hd : 1 ≤ d)
    (μ : ContinuousMultilinearMap K (fun _ : Fin d => lp (fun _ : I => K) ∞) K) :
    Tendsto (fun i : I => μ (fun _ => lp.single ∞ i (1 : K))) cofinite (𝓝 0) :=
  AlternatingAnalytic.Tails.multilinear_diagonal_tendsto_zero hK hd μ

end AlternatingAnalyticChallenge.LemF_2
