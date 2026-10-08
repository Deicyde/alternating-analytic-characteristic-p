import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# Theorem 4.4 (finite-coordinate parameters), pp. 10-11

Paper statement (Section 4.2, `thm:finite-parameters`): Let `j : W → Z` be a closed linear
isometry. If `P` is boundedly linearly isomorphic to `K^d` and `U ⊆ P` is open, then
`f : U → W` is analytic if and only if `jf` is analytic. For the maximum norm on `K^d`, ambient
coefficients `b_n` can be replaced by `W`-valued coefficients `q_n` with
`‖q_n‖ ≤ d^n ‖b_n‖` (`n ≥ 1`). If `Z` is nonarchimedean, the factor `d^n` can be replaced by `1`.

Standing hypotheses (Section 3, p. 6): `K` is a nontrivially normed field, `P, W, Z` are normed
`K`-spaces, `j : W → Z` is a linear isometry with closed range; none of these is assumed
complete. An *ambient expansion* of `f` at `x₀` (eq. (3.1)) is `jf(x₀ + h) = ∑ b_n(h, …, h)` with
bounded `n`-linear `b_n : P^n → Z` and `sup_n ‖b_n‖ R^n < ∞` for some `R > 0`.

## Formalization notes
* `j` is `W →ₗᵢ[K] Z` with `IsClosed (Set.range j)`; "boundedly linearly isomorphic" is a
  continuous linear equivalence `e : P ≃L[K] (Fin d → K)`. No completeness of `K, P, W, Z`.
* `f : U → W` on an open `U` is modelled, as usual in Mathlib, by `f : P → W` together with
  `IsOpen U`; values of `f` outside `U` are irrelevant. "Analytic" on the open set `U` is
  `AnalyticOnNhd K · U` (analytic at every point of `U`). The hypothesis `IsOpen U` is kept
  from the paper although the pointwise formulation does not need it. "Analytic" is the
  pointwise power-series notion of Section 3 (p. 7), analytic at every point of `U`, not the
  `C^ω` manifold regularity class of the Section 2 convention.
* Parts 2 and 3 are stated for `P = Fin d → K`, whose Mathlib norm is the maximum norm. An
  ambient expansion of `jf` at `x₀` is `HasFPowerSeriesAt (j ∘ f) b x₀` with
  `b : FormalMultilinearSeries K (Fin d → K) Z` (Mathlib's notion: summability on a ball of
  positive radius, which is equivalent to the geometric bound of (3.1) after shrinking `R`).
  "`b_n` can be replaced by `W`-valued `q_n`" is formalized as: there is a `W`-valued formal
  multilinear series `q` with the same diagonals, `j (q_n (h, …, h)) = b_n (h, …, h)`, which is
  itself a power series of `f` at `x₀` (`HasFPowerSeriesAt f q x₀`), and with the stated bound.
* Part 2 bound: `‖q n‖ ≤ d^n ‖b n‖` for `n ≥ 1`. Part 3 (with `[IsUltrametricDist Z]`):
  `‖q n‖ ≤ ‖b n‖` for `n ≥ 1`.
-/

namespace AlternatingAnalyticChallenge.Thm4_4

universe uK uP uW uZ

/-- **Theorem 4.4 (1).** With finitely many continuous coordinates on the parameter space,
analyticity on an open set reflects through a closed linear isometry. -/
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

/-- **Theorem 4.4 (2).** For the maximum norm on `K^d`, the ambient coefficients `b_n` of an
expansion of `j ∘ f` can be replaced by `W`-valued coefficients `q_n`, with the same diagonals,
forming an expansion of `f`, and with `‖q_n‖ ≤ d^n ‖b_n‖` for `n ≥ 1`. -/
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

/-- **Theorem 4.4 (3).** If `Z` is nonarchimedean, the factor `d^n` in part (2) can be replaced
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
