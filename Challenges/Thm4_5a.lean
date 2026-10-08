import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Within
import Mathlib.Analysis.Normed.Group.Ultra

/-!
# Theorem 4.5(1) (summable parameter spaces: c₀), p. 11

Paper statement (Section 4.2, `thm:summable-parameters`, part (1)): Let `j : W → Z` be a closed
linear isometry. Suppose `K` and `Z` are nonarchimedean and `W` is complete. For `U ⊆ c₀(I, K)`
open, analyticity of `j f` implies analyticity of `f : U → W`. Coefficients can be lifted without
increasing their norms. Here `c₀` carries the supremum norm. The field need not be complete.
Each assertion remains valid for a parameter space that is a bounded linear retract of the
indicated space.

## Formalization notes
* `c₀(I, K)` is Mathlib's `C₀(I, K)` (continuous functions vanishing at infinity) for an
  arbitrary index type `I` with the discrete topology; its norm is the supremum norm.
* "Nonarchimedean" is `IsUltrametricDist`. The hypothesis `[IsUltrametricDist K]` is included
  because the paper assumes it; the library proof does not use it (the library is stronger).
* A closed linear isometry is `j : W →ₗᵢ[K] Z` together with `IsClosed (Set.range j)` (the
  closedness hypothesis is also stated although it follows from completeness of `W`).
* `f : U → W` is modelled as a total map `f : C₀(I, K) → W` with `AnalyticOn K _ U` on the open
  set `U` (only the values on `U` matter).
* "Analytic" for the composite is Mathlib `AnalyticOn` on the open set `U` (equivalent to
  `AnalyticOnNhd` there).
* "Coefficients can be lifted without increasing their norms" is stated at a point `x ∈ U`:
  for every power series `p` of `j ∘ f` on a ball `B(x, r)` there is a `W`-valued series `q`
  with the same diagonals, `‖q n‖ ≤ ‖p n‖`, representing `f` on the same ball. As in the paper's
  proof (Theorem 3.1), only diagonals are lifted, since the non-symmetric parts of `p n` need not
  take values in `W`. The binders `U`, `hU`, `x ∈ U` of this theorem are kept only to mirror the
  paper's setting; the lift holds at any point where `j ∘ f` has a power series on a ball.
* The retract clause is stated for the analyticity assertion only: `P` is a normed space with
  bounded linear `i : P → c₀(I, K)`, `r : c₀(I, K) → P`, `r ∘ i = id`. The norm-nonincreasing
  coefficient clause is not claimed for retracts (on a retract the natural bound picks up
  factors `‖r‖ⁿ ‖i‖ⁿ`), and the paper's sentence does not specify a bound there.
* No completeness of `K`, `Z` or `P` is assumed.
-/

open scoped ZeroAtInfty

namespace AlternatingAnalyticChallenge.Thm4_5a

universe uI uK uW uZ uP

/-- **Theorem 4.5(1), analyticity.** `K` and `Z` nonarchimedean, `W` complete,
`j : W → Z` a closed linear isometry, `U ⊆ c₀(I, K)` open: if `j ∘ f` is analytic on `U`,
then `f` is analytic on `U`. -/
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

/-- **Theorem 4.5(1), coefficient lifting.** Under the same hypotheses, every power series
`p` of `j ∘ f` on a ball `B(x, r)` with `x ∈ U` can be replaced by a `W`-valued power series `q`
with the same diagonals (`j (q n (y, …, y)) = p n (y, …, y)`) and no larger coefficient norms
(`‖q n‖ ≤ ‖p n‖`), which represents `f` on the same ball. -/
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

/-- **Theorem 4.5(1), bounded linear retract clause.** The analyticity assertion remains valid
for a parameter space `P` that is a bounded linear retract of `c₀(I, K)`: `i : P → c₀(I, K)` and
`r : c₀(I, K) → P` bounded linear with `r ∘ i = id_P`. -/
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
