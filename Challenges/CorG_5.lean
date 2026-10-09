import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Corollary G.5 (entire polynomial approximation of a nonanalytic smooth map), p. 56

Paper statement: "Let K be a complete nonarchimedean nontrivially normed field and put
P = ℓ¹(ℕ,K), with the ordinary sum norm. There are Banach spaces W ⊆ Z, with W closed, and a
map f on the open unit ball of P such that f is analytic into Z and C^∞ into W, but is not
analytic into W at zero. Moreover, f is a uniform limit on every smaller ball of entire
W-valued polynomials."

## Formalization notes

* `P` is Mathlib's `lp (fun _ : ℕ => K) 1`.
* `Z` is required to lie in `Type uK`, the universe of `P`, which contains the paper's witness.
* `f` is a total map `P → W`; all conditions on it are imposed on `Metric.ball 0 1`.
* An entire `W`-valued polynomial is `x ↦ ∑_{i < d} q i (x, …, x)` for a
  `FormalMultilinearSeries` `q`.
* One sequence of polynomials converges to `f` uniformly on `Metric.closedBall 0 r` for every
  `0 < r < 1`.
-/

open Filter
open scoped ContDiff

namespace AlternatingAnalyticChallenge.CorG_5

universe uK

/-- Corollary G.5: on the unit ball of `ℓ¹(ℕ,K)` there is a map that is analytic into `Z`,
`C^∞` into a closed subspace `W`, not analytic into `W` at `0`, and a uniform limit on smaller
balls of entire `W`-valued polynomials. -/
theorem exists_smooth_nonanalytic_polynomial_limit
    (K : Type uK) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] :
    ∃ (Z : Type uK) (_ : NormedAddCommGroup Z) (_ : NormedSpace K Z) (_ : CompleteSpace Z)
      (W : Submodule K Z), IsClosed (W : Set Z) ∧
      ∃ f : lp (fun _ : ℕ => K) 1 → W,
        AnalyticOnNhd K (fun x => (f x : Z)) (Metric.ball 0 1) ∧
        ContDiffOn K ∞ f (Metric.ball 0 1) ∧
        ¬ AnalyticAt K f 0 ∧
        ∃ g : ℕ → lp (fun _ : ℕ => K) 1 → W,
          (∀ N : ℕ, ∃ (d : ℕ) (q : FormalMultilinearSeries K (lp (fun _ : ℕ => K) 1) W),
            ∀ x, g N x = ∑ i ∈ Finset.range d, q i (fun _ => x)) ∧
          ∀ r : ℝ, 0 < r → r < 1 →
            TendstoUniformlyOn g f atTop (Metric.closedBall 0 r) := by
  sorry

end AlternatingAnalyticChallenge.CorG_5
