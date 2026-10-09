import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# Theorem 3.1 (the coefficient descent criterion), p. 7

Standing assumptions of Section 3: "`K` is nontrivially normed, `P, W, Z` are normed `K`-spaces,
and `j : W → Z` is a linear isometry with closed range. None of these spaces is assumed complete."
If `U ⊆ P` is open and `f : U → W`, an ambient expansion at `x₀ ∈ U` means (3.1)
`j f(x₀ + h) = ∑_{n ≥ 0} b_n(h, …, h)`, `sup_n ‖b_n‖ Rⁿ < ∞`, for some `R > 0`, with bounded
`n`-linear `b_n : Pⁿ → Z` and convergence to the displayed value for `‖h‖ < R`.

Paper statement: "Suppose (3.1) holds. Then every diagonal `b_n(h, …, h)` belongs to `j(W)`.
The map `f` is analytic at `x₀` if and only if there are bounded `n`-linear maps
`q_n : Pⁿ → W` and `r > 0` such that `j q_n(h, …, h) = b_n(h, …, h)` (`n ≥ 0`, `h ∈ P`),
`sup_n ‖q_n‖ rⁿ < ∞`. Only the diagonals must agree; the original mixed values of `b_n` need
not lie in `j(W)`."

## Formalization notes
* The open set `U` is dropped: `f` is a total function `P → W`. The statement only uses `f` on
  the ball `‖h‖ < R` and its germ at `x₀`, so this loses nothing.
* The coefficients `b_n` and `q_n` are `FormalMultilinearSeries`; the bounds
  `sup_n ‖b_n‖ Rⁿ < ∞` are `BddAbove (Set.range fun n => ‖b n‖ * R ^ n)`.
* Convergence is `HasSum`. Under the bound and `‖h‖ < R` the terms are dominated by a geometric
  sequence, so this agrees with convergence of the partial sums.
* "Analytic at `x₀`" is Mathlib's `AnalyticAt K f x₀`.
* The last sentence of the statement is a remark and is not formalized.
-/

namespace AlternatingAnalyticChallenge.Thm3_1

variable {K : Type*} [NontriviallyNormedField K]
  {P W Z : Type*} [NormedAddCommGroup P] [NormedSpace K P]
  [NormedAddCommGroup W] [NormedSpace K W] [NormedAddCommGroup Z] [NormedSpace K Z]

/-- Every diagonal of an ambient expansion lies in `j(W)`. -/
theorem part1 (j : W →ₗᵢ[K] Z) (hj : IsClosed (Set.range j))
    (f : P → W) (x₀ : P) (b : FormalMultilinearSeries K P Z) (R : ℝ) (hR : 0 < R)
    (hbound : BddAbove (Set.range fun n => ‖b n‖ * R ^ n))
    (hexp : ∀ h : P, ‖h‖ < R → HasSum (fun n => b n (fun _ => h)) (j (f (x₀ + h)))) :
    ∀ (n : ℕ) (h : P), b n (fun _ => h) ∈ Set.range j := by
  sorry

/-- `f` is analytic at `x₀` if and only if the ambient diagonals have
`W`-valued bounded multilinear representatives with a positive common radius. -/
theorem part2 (j : W →ₗᵢ[K] Z) (hj : IsClosed (Set.range j))
    (f : P → W) (x₀ : P) (b : FormalMultilinearSeries K P Z) (R : ℝ) (hR : 0 < R)
    (hbound : BddAbove (Set.range fun n => ‖b n‖ * R ^ n))
    (hexp : ∀ h : P, ‖h‖ < R → HasSum (fun n => b n (fun _ => h)) (j (f (x₀ + h)))) :
    AnalyticAt K f x₀ ↔
      ∃ (q : FormalMultilinearSeries K P W) (r : ℝ), 0 < r ∧
        (∀ (n : ℕ) (h : P), j (q n (fun _ => h)) = b n (fun _ => h)) ∧
        BddAbove (Set.range fun n => ‖q n‖ * r ^ n) := by
  sorry

end AlternatingAnalyticChallenge.Thm3_1
