import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Within
import Mathlib.Analysis.Normed.Group.Ultra
import AlternatingAnalytic.Analysis.CZeroReflection

/-!
# Theorem 4.5(1) (summable parameter spaces: c₀), p. 11

Solution: identical statements to `Challenges/Thm4_5a.lean`, proved from
`AlternatingAnalytic.c0_analyticOn_linearIsometry`,
`AlternatingAnalytic.c0_exists_hasFPowerSeriesOnBall_linearIsometry` and
`AlternatingAnalytic.c0_analyticOnNhd_linearIsometry` (`Analysis/CZeroReflection.lean`).
The retract clause is not in the library; it is derived here in a few lines
(pull back along `r`, reflect on `c₀`, restrict along `i`), exactly as in the paper's proof.
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
  exact AlternatingAnalytic.c0_analyticOn_linearIsometry j hU hf

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
  obtain ⟨q, hnorm, hdiag, _, hq⟩ :=
    AlternatingAnalytic.c0_exists_hasFPowerSeriesOnBall_linearIsometry j hp
  exact ⟨q, hnorm, hdiag, hq⟩

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
  have hri_apply (x : P) : r (i x) = x := DFunLike.congr_fun hri x
  have hpull : AnalyticOnNhd K (j ∘ (f ∘ r)) (r ⁻¹' U) :=
    (hU.analyticOn_iff_analyticOnNhd.mp hf).comp (r.analyticOnNhd _) (fun _ hx => hx)
  have hfr : AnalyticOnNhd K (f ∘ r) (r ⁻¹' U) :=
    AlternatingAnalytic.c0_analyticOnNhd_linearIsometry j hpull
  have hmaps : Set.MapsTo i U (r ⁻¹' U) := by
    intro x hx
    change r (i x) ∈ U
    rwa [hri_apply]
  have hcomp : (f ∘ r) ∘ i = f := by
    funext x
    exact congrArg f (hri_apply x)
  have h := hfr.comp (i.analyticOnNhd U) hmaps
  rw [hcomp] at h
  exact h.analyticOn

end AlternatingAnalyticChallenge.Thm4_5a
