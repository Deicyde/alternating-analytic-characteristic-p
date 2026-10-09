import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Within
import Mathlib.Analysis.Normed.Group.Ultra
import AlternatingAnalytic.Analysis.CZeroReflection

/-!
# Proof of Theorem 4.5(1)

Uses `c0_analyticOn_linearIsometry`, `c0_exists_hasFPowerSeriesOnBall_linearIsometry` and
`c0_analyticOnNhd_linearIsometry` (`Analysis/CZeroReflection.lean`). The retract clause is
proved here: pull back along `r`, reflect on `c₀`, restrict along `i`.
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
  exact AlternatingAnalytic.c0_analyticOn_linearIsometry j hU hf

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
  obtain ⟨q, hnorm, hdiag, _, hq⟩ :=
    AlternatingAnalytic.c0_exists_hasFPowerSeriesOnBall_linearIsometry j hp
  exact ⟨q, hnorm, hdiag, hq⟩

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
