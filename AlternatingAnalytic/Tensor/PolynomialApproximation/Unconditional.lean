/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
import AlternatingAnalytic.Tensor.PolynomialApproximation.Corollary
import AlternatingAnalytic.Tensor.L1Projection.Optimal

/-!
# Corollary G.5

Corollary G.5 for `P = ℓ¹(ℕ,K)`: the conditional statement of `Corollary.lean` with its
hypothesis, the factorial lower bound on projection norms, discharged by Proposition G.4
(`L1Projection.factorial_le_norm_of_projection`). The two spellings of `T_n(P)` and `Δ_n(P)` (the
library's `HomogeneousTensorReflection` and the universe-polymorphic copies of `L1Projection`)
agree definitionally.
-/

open Filter
open scoped ContDiff

namespace AlternatingAnalytic.PolynomialApproximation

universe uK

/-- The factorial lower bound of Proposition G.4 for projections onto the diagonal span of the
library tensor powers of `ℓ¹(ℕ,K)`. -/
theorem factorial_le_norm_projection_l1
    (K : Type uK) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (n : ℕ) (R : TensorPower K (lp (fun _ : ℕ => K) 1) n →L[K]
        DiagonalSpan K (lp (fun _ : ℕ => K) 1) n)
    (hR : ∀ t : DiagonalSpan K (lp (fun _ : ℕ => K) 1) n,
        R (t : TensorPower K (lp (fun _ : ℕ => K) 1) n) = t) :
    (n.factorial : ℝ) ≤ ‖R‖ :=
  L1Projection.factorial_le_norm_of_projection (K := K) (I := ℕ) n R hR

/-- **Corollary G.5.** On the unit ball of `ℓ¹(ℕ,K)` over a complete nonarchimedean field there
is a map analytic into `Z`, `C^∞` into a closed subspace `W`, not analytic into `W` at `0`, and a
locally uniform limit of entire `W`-valued polynomials. -/
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
  exists_smooth_nonanalytic_polynomial_limit_of_factorial_le K
    (fun n _ R hR => factorial_le_norm_projection_l1 K n R hR)

end AlternatingAnalytic.PolynomialApproximation
