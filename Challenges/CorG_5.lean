import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Corollary G.5 (entire polynomial approximation of a nonanalytic smooth map), p. 55

Paper statement: "Let K be a complete nonarchimedean nontrivially normed field and put
P = ℓ¹(ℕ,K), with the ordinary sum norm. There are Banach spaces W ⊆ Z, with W closed, and a
map f on the open unit ball of P such that f is analytic into Z and C^∞ into W, but is not
analytic into W at zero. Moreover, f is a uniform limit on every smaller ball of entire
W-valued polynomials."
(The paper's witness: `Z = c₀({T_n(P)}_{n ≥ 1})`, `W = c₀({Δ_n(P)}_{n ≥ 1})`,
`f(x) = (x^{⊗ n})_{n ≥ 1}`, with truncations `f_N` and error `≤ r^{N+1}` on `‖x‖ ≤ r`.)

Formalization notes:
* `K : Type uK` with `[NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]`;
  `P = lp (fun _ : ℕ => K) 1` (Mathlib's `ℓ¹` with the sum norm).
* "Banach spaces W ⊆ Z, W closed": an existential complete normed space `Z : Type uK` (the
  universe of `P`, which contains the paper's witness) and a closed `W : Submodule K Z`;
  `W` is then complete with the subspace norm.
* "A map f on the open unit ball": a total map `f : P → W`; all regularity conditions are
  imposed on `Metric.ball 0 1` only. "Analytic into Z" is `AnalyticOnNhd K (↑ ∘ f)` on the
  ball; "C^∞ into W" is `ContDiffOn K ∞ f` on the ball; "not analytic into W at zero" is
  `¬ AnalyticAt K f 0`.
* "Entire W-valued polynomial": a map `x ↦ ∑_{i < d} q i (x, …, x)` for a formal multilinear
  series `q` of bounded multilinear maps `P^i → W` (a finite sum of bounded homogeneous
  polynomials).
* "Uniform limit on every smaller ball": one sequence `g N` of entire polynomials converging
  to `f` uniformly on `Metric.closedBall 0 r` for every `0 < r < 1` (the paper's proof
  produces a single sequence, the truncations; closed balls also cover the open ones).
* No definitions are introduced.
* Status: not formalized in the library. `AlternatingAnalytic/Analysis/TensorTestFamily.lean`
  constructs the paper's witness `tensorTestMap` (into the dependent `c₀` sum of tensor powers,
  valued in the diagonal subspace) and proves its ambient analyticity on the unit ball
  (`tensorTestMap_analyticOnNhd`, `tensor_test_family`), but the nonanalyticity into `W`
  (which needs Proposition G.4), the `C^∞` statement and the polynomial approximation are not
  formalized.
-/

open Filter
open scoped ContDiff

namespace AlternatingAnalyticChallenge.CorG_5

universe uK

/-- **Corollary G.5.** Over a complete nonarchimedean field, on the unit ball of `ℓ¹(ℕ,K)`
there is a map that is analytic into a Banach space `Z` and `C^∞` into a closed subspace `W`,
not analytic into `W` at `0`, and a locally uniform limit of entire `W`-valued polynomials. -/
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
