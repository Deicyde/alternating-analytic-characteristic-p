import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.UniformSpace.UniformConvergence
import AlternatingAnalytic.Tensor.PolynomialApproximation.Unconditional

/-!
# Proof of Corollary G.5

Uses `AlternatingAnalytic.PolynomialApproximation.exists_smooth_nonanalytic_polynomial_limit`
from `AlternatingAnalytic/Tensor/PolynomialApproximation/Unconditional.lean`.
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
            TendstoUniformlyOn g f atTop (Metric.closedBall 0 r) :=
  AlternatingAnalytic.PolynomialApproximation.exists_smooth_nonanalytic_polynomial_limit K

end AlternatingAnalyticChallenge.CorG_5
