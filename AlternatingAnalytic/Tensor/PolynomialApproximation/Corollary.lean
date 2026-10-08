/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
import AlternatingAnalytic.Tensor.PolynomialApproximation.TensorTestMap
import Mathlib.Analysis.Normed.Group.Ultra

/-!
# Corollary G.5, conditional on the factorial projection bound

The statement of Corollary G.5 for `P = ℓ¹(ℕ,K)`, with the witness `Z` the dependent `c₀` sum of
tensor powers, `W` its closed diagonal subspace, `f` the tensor test map and the truncations as
approximating polynomials. The only input not yet in the library is the lower bound of
Proposition G.4: every projection `T_n(P) → Δ_n(P)` with `1 ≤ n` has norm at least `n!`. It is a
hypothesis here; `factorial_le_norm_of_sInf_eq` derives it from the infimum form of
Proposition G.4.
-/

open Filter
open scoped ContDiff

namespace AlternatingAnalytic.PolynomialApproximation

universe uK

/-- **Corollary G.5**, assuming the factorial lower bound on projection norms of
Proposition G.4 for `ℓ¹(ℕ,K)`. -/
theorem exists_smooth_nonanalytic_polynomial_limit_of_factorial_le
    (K : Type uK) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (hproj : ∀ n : ℕ, 1 ≤ n →
      ∀ R : TensorPower K (lp (fun _ : ℕ => K) 1) n →L[K]
        DiagonalSpan K (lp (fun _ : ℕ => K) 1) n,
      (∀ t : DiagonalSpan K (lp (fun _ : ℕ => K) 1) n,
        R (t : TensorPower K (lp (fun _ : ℕ => K) 1) n) = t) →
      (n.factorial : ℝ) ≤ ‖R‖) :
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
  ⟨tensorTestSpace K (lp (fun _ : ℕ => K) 1), inferInstance, inferInstance, inferInstance,
    tensorTestSubmodule, isClosed_tensorTestSubmodule, tensorTestMap,
    tensorTestMap_analyticOnNhd, tensorTestMap_contDiffOn ⊤,
    not_analyticAt_tensorTestMap_of_factorial_le hproj, tensorTestTruncation,
    fun N => ⟨N, tensorTestLiftSeries, fun _ => rfl⟩,
    fun _ _ hr => tendstoUniformlyOn_tensorTestTruncation hr⟩

end AlternatingAnalytic.PolynomialApproximation
