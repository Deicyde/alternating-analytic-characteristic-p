import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Within
import Mathlib.Analysis.Normed.Group.Ultra

/-!
# Theorem 4.5(1) (summable parameter spaces: c₀), pp. 11-12

Paper statement (Section 4.2, part (1)): Let `j : W → Z` be a closed
linear isometry. Suppose `K` and `Z` are nonarchimedean and `W` is complete. For `U ⊆ c₀(I, K)`
open, analyticity of `j f` implies analyticity of `f : U → W`. Coefficients can be lifted without
increasing their norms. Here `c₀` carries the supremum norm. The field need not be complete.
Each analyticity assertion remains valid for a parameter space `P` that is a bounded linear
retract of the indicated space `V`, with bounded linear `i : P → V`, `r : V → P` and `r i = id_P`;
in (1) the lifted coefficients then satisfy `‖q_n‖ ≤ (‖r‖ ‖i‖)^n ‖b_n‖`.

## Formalization notes
* `c₀(I, K)` is Mathlib's `C₀(I, K)` for an index type `I` with the discrete topology; its norm
  is the supremum norm.
* "Nonarchimedean" is `IsUltrametricDist`. A closed linear isometry is `j : W →ₗᵢ[K] Z` with
  `IsClosed (Set.range j)`, kept although it follows from completeness of `W`.
* `f : U → W` is `f : C₀(I, K) → W` with `IsOpen U`; "analytic on `U`" is `AnalyticOn K · U`.
* Coefficient lifting is stated at `x ∈ U` for a power series `p` of `j ∘ f` on a ball
  `B(x, r)`: a `W`-valued `q` with the same diagonals, `‖q n‖ ≤ ‖p n‖`, representing `f` on the
  same ball. Only diagonals are lifted, as in the proof of Theorem 3.1.
* The retract clause is stated for analyticity only, with bounded linear `i : P → c₀(I, K)`,
  `r : c₀(I, K) → P`, `r ∘ i = id`; the paper's coefficient bound
  `‖q_n‖ ≤ (‖r‖ ‖i‖)^n ‖b_n‖` on retracts is not stated.
-/

open scoped ZeroAtInfty

namespace AlternatingAnalyticChallenge.Thm4_5a

universe uI uK uW uZ uP

/-- Theorem 4.5(1), analyticity: if `j ∘ f` is analytic on an open `U ⊆ c₀(I, K)`, so is `f`. -/
theorem c0_analyticOn_of_analyticOn_comp_closed_isometry
    {I : Type uI} [TopologicalSpace I] [DiscreteTopology I]
    {K : Type uK} [NontriviallyNormedField K] [IsUltrametricDist K]
    {W : Type uW} [NormedAddCommGroup W] [NormedSpace K W] [CompleteSpace W]
    {Z : Type uZ} [NormedAddCommGroup Z] [NormedSpace K Z] [IsUltrametricDist Z]
    (j : W →ₗᵢ[K] Z) (hj : IsClosed (Set.range j))
    {U : Set C₀(I, K)} (hU : IsOpen U) {f : C₀(I, K) → W}
    (hf : AnalyticOn K (j ∘ f) U) :
    AnalyticOn K f U := by
  sorry

/-- Theorem 4.5(1), coefficients: a power series of `j ∘ f` on a ball lifts to a `W`-valued
power series of `f` on the same ball, with the same diagonals and no larger norms. -/
theorem c0_coefficients_lift_without_increasing_norms
    {I : Type uI} [TopologicalSpace I] [DiscreteTopology I]
    {K : Type uK} [NontriviallyNormedField K] [IsUltrametricDist K]
    {W : Type uW} [NormedAddCommGroup W] [NormedSpace K W] [CompleteSpace W]
    {Z : Type uZ} [NormedAddCommGroup Z] [NormedSpace K Z] [IsUltrametricDist Z]
    (j : W →ₗᵢ[K] Z) (hj : IsClosed (Set.range j))
    {U : Set C₀(I, K)} (hU : IsOpen U) {f : C₀(I, K) → W}
    {x : C₀(I, K)} (hx : x ∈ U) {r : ENNReal}
    {p : FormalMultilinearSeries K C₀(I, K) Z}
    (hp : HasFPowerSeriesOnBall (j ∘ f) p x r) :
    ∃ q : FormalMultilinearSeries K C₀(I, K) W,
      (∀ n, ‖q n‖ ≤ ‖p n‖) ∧
      (∀ n y, j (q n (fun _ => y)) = p n (fun _ => y)) ∧
      HasFPowerSeriesOnBall f q x r := by
  sorry

/-- Theorem 4.5(1), retracts: the analyticity assertion holds on a bounded linear retract `P`
of `c₀(I, K)`. -/
theorem c0_retract_analyticOn_of_analyticOn_comp_closed_isometry
    {I : Type uI} [TopologicalSpace I] [DiscreteTopology I]
    {K : Type uK} [NontriviallyNormedField K] [IsUltrametricDist K]
    {W : Type uW} [NormedAddCommGroup W] [NormedSpace K W] [CompleteSpace W]
    {Z : Type uZ} [NormedAddCommGroup Z] [NormedSpace K Z] [IsUltrametricDist Z]
    {P : Type uP} [NormedAddCommGroup P] [NormedSpace K P]
    (i : P →L[K] C₀(I, K)) (r : C₀(I, K) →L[K] P)
    (hri : r.comp i = ContinuousLinearMap.id K P)
    (j : W →ₗᵢ[K] Z) (hj : IsClosed (Set.range j))
    {U : Set P} (hU : IsOpen U) {f : P → W}
    (hf : AnalyticOn K (j ∘ f) U) :
    AnalyticOn K f U := by
  sorry

end AlternatingAnalyticChallenge.Thm4_5a
