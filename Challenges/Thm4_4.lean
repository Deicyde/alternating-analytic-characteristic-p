import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# Theorem 4.4 (finite-coordinate parameters), pp. 10-11

Paper statement (Section 4.2): Let `j : W → Z` be a closed linear
isometry. If `P` is boundedly linearly isomorphic to `K^d` and `U ⊆ P` is open, then
`f : U → W` is analytic if and only if `jf` is analytic. For the maximum norm on `K^d`, ambient
coefficients `b_n` can be replaced by `W`-valued coefficients `q_n` with
`‖q_n‖ ≤ d^n ‖b_n‖` (`n ≥ 1`). If `Z` is nonarchimedean, the factor `d^n` can be replaced by `1`.

## Formalization notes
* `K` is a nontrivially normed field and `P, W, Z` are normed `K`-spaces, none assumed complete,
  as in Section 3.
* `j` is `W →ₗᵢ[K] Z` with `IsClosed (Set.range j)`; "boundedly linearly isomorphic" is
  `e : P ≃L[K] (Fin d → K)`.
* `f : U → W` is `f : P → W` with `IsOpen U`. "Analytic on `U`" is `AnalyticOnNhd K · U`, the
  pointwise power-series notion of Section 3.
* Parts 2 and 3 take `P = Fin d → K`, whose Mathlib norm is the maximum norm.
* The ambient expansion (3.1) of `jf` at `x₀` is `HasFPowerSeriesAt (j ∘ f) b x₀`; Mathlib's
  summability on a ball is equivalent to the geometric bound of (3.1) after shrinking `R`.
* "`b_n` can be replaced by `q_n`": a `W`-valued series `q` with `j (q_n (h, …, h)) = b_n (h, …, h)`,
  `HasFPowerSeriesAt f q x₀`, and the stated bound.
-/

namespace AlternatingAnalyticChallenge.Thm4_4

universe uK uP uW uZ

/-- Theorem 4.4(1): with finitely many continuous coordinates on `P`, `f` is analytic on `U`
iff `j ∘ f` is. -/
theorem part1_analyticOnNhd_iff
    (K : Type uK) [NontriviallyNormedField K]
    {P : Type uP} {W : Type uW} {Z : Type uZ}
    [NormedAddCommGroup P] [NormedSpace K P]
    [NormedAddCommGroup W] [NormedSpace K W]
    [NormedAddCommGroup Z] [NormedSpace K Z]
    (j : W →ₗᵢ[K] Z) (hj : IsClosed (Set.range j))
    {d : ℕ} (e : P ≃L[K] (Fin d → K))
    {U : Set P} (hU : IsOpen U) (f : P → W) :
    AnalyticOnNhd K f U ↔ AnalyticOnNhd K (j ∘ f) U := by
  sorry

/-- Theorem 4.4(2): the coefficients of an expansion of `j ∘ f` lift to an expansion of `f`
with the same diagonals and `‖q_n‖ ≤ d^n ‖b_n‖` for `n ≥ 1`. -/
theorem part2_coefficient_bound
    (K : Type uK) [NontriviallyNormedField K]
    {W : Type uW} {Z : Type uZ}
    [NormedAddCommGroup W] [NormedSpace K W]
    [NormedAddCommGroup Z] [NormedSpace K Z]
    (j : W →ₗᵢ[K] Z) (hj : IsClosed (Set.range j))
    {d : ℕ} {f : (Fin d → K) → W} {x₀ : Fin d → K}
    {b : FormalMultilinearSeries K (Fin d → K) Z}
    (hb : HasFPowerSeriesAt (j ∘ f) b x₀) :
    ∃ q : FormalMultilinearSeries K (Fin d → K) W,
      (∀ n (h : Fin d → K), j (q n (fun _ => h)) = b n (fun _ => h)) ∧
      HasFPowerSeriesAt f q x₀ ∧
      ∀ n, 1 ≤ n → ‖q n‖ ≤ (d : ℝ) ^ n * ‖b n‖ := by
  sorry

/-- Theorem 4.4(3): if `Z` is nonarchimedean, the factor `d^n` in part (2) can be replaced
by `1`. -/
theorem part3_coefficient_bound_ultrametric
    (K : Type uK) [NontriviallyNormedField K]
    {W : Type uW} {Z : Type uZ}
    [NormedAddCommGroup W] [NormedSpace K W]
    [NormedAddCommGroup Z] [NormedSpace K Z] [IsUltrametricDist Z]
    (j : W →ₗᵢ[K] Z) (hj : IsClosed (Set.range j))
    {d : ℕ} {f : (Fin d → K) → W} {x₀ : Fin d → K}
    {b : FormalMultilinearSeries K (Fin d → K) Z}
    (hb : HasFPowerSeriesAt (j ∘ f) b x₀) :
    ∃ q : FormalMultilinearSeries K (Fin d → K) W,
      (∀ n (h : Fin d → K), j (q n (fun _ => h)) = b n (fun _ => h)) ∧
      HasFPowerSeriesAt f q x₀ ∧
      ∀ n, 1 ≤ n → ‖q n‖ ≤ ‖b n‖ := by
  sorry

end AlternatingAnalyticChallenge.Thm4_4
