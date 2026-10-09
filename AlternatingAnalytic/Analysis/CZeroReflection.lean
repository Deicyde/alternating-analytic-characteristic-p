import AlternatingAnalytic.Analysis.CZeroCoefficients
import AlternatingAnalytic.Analysis.FiniteCoordinateRadius

/-!
# Analytic reflection from discrete c₀ with unchanged radius

Let `j : W → Z` be a linear isometry from a complete space into an ultrametric
space. If `j ∘ f` has a power series on a ball in `C₀(I, K)`, then so does `f`,
with coefficients of no larger norm and the same diagonals, on the same ball.
This is Theorem 4.5(1). The scalar field and `Z` need not be complete.
-/

noncomputable section

open scoped Topology NNReal ENNReal ZeroAtInfty

namespace AlternatingAnalytic

variable {I K Z W E : Type*} [TopologicalSpace I] [DiscreteTopology I]
  [NontriviallyNormedField K]
  [NormedAddCommGroup Z] [NormedSpace K Z] [IsUltrametricDist Z]
  [NormedAddCommGroup W] [NormedSpace K W] [CompleteSpace W]
  [NormedAddCommGroup E] [NormedSpace K E]

/-- A power series on c₀ for a map into a complete subspace of an ultrametric space
lifts to the subspace on the same ball, with the same diagonals and no larger
coefficient norms. -/
theorem c0_exists_hasFPowerSeriesOnBall_subtype
    (S : Submodule K Z) [CompleteSpace S]
    {f : C₀(I, K) → S} {x : C₀(I, K)} {r : ℝ≥0∞}
    {p : FormalMultilinearSeries K C₀(I, K) Z}
    (hp : HasFPowerSeriesOnBall (fun y => (f y : Z)) p x r) :
    ∃ q : FormalMultilinearSeries K C₀(I, K) S,
      (∀ n, ‖q n‖ ≤ ‖p n‖) ∧
      (∀ n y, (q n (fun _ => y) : Z) = p n (fun _ => y)) ∧
      p.radius ≤ q.radius ∧ HasFPowerSeriesOnBall f q x r := by
  classical
  have hS : IsClosed (S : Set Z) := by
    simpa using S.subtypeₗᵢ.isometry.isClosedEmbedding.isClosed_range
  have hmem (n : ℕ) (y : C₀(I, K)) : p n (fun _ => y) ∈ S :=
    HasFPowerSeriesAt.diagonal_mem_closedSubspace S hS hp.hasFPowerSeriesAt
      (Filter.Eventually.of_forall fun z => (f z).property) n y
  choose q hdiag hnorm using fun n =>
    CZero.homogeneous_diagonal_lifting S (p n) (hmem n)
  exact ⟨q, hnorm, hdiag, FormalMultilinearSeries.radius_le_of_le hnorm,
    hasFPowerSeriesOnBall_subtype_of_diagonal_of_norm_le S hp q hnorm hdiag⟩

/-- Analytic reflection on c₀ through a linear isometry from a complete space into
an ultrametric space, keeping the ball and the coefficient bounds. -/
theorem c0_exists_hasFPowerSeriesOnBall_linearIsometry
    (j : W →ₗᵢ[K] Z) {f : C₀(I, K) → W} {x : C₀(I, K)} {r : ℝ≥0∞}
    {p : FormalMultilinearSeries K C₀(I, K) Z}
    (hp : HasFPowerSeriesOnBall (j ∘ f) p x r) :
    ∃ q : FormalMultilinearSeries K C₀(I, K) W,
      (∀ n, ‖q n‖ ≤ ‖p n‖) ∧
      (∀ n y, j (q n (fun _ => y)) = p n (fun _ => y)) ∧
      p.radius ≤ q.radius ∧ HasFPowerSeriesOnBall f q x r := by
  let : CompleteSpace j.range := j.equivRange.symm.toIsometryEquiv.completeSpace
  let g : C₀(I, K) → j.range := fun y => j.equivRange (f y)
  obtain ⟨q, hnorm, hdiag, _, hq⟩ :=
    c0_exists_hasFPowerSeriesOnBall_subtype j.range (f := g) hp
  let e := j.equivRange.symm.toLinearIsometry
  let q' := e.toContinuousLinearMap.compFormalMultilinearSeries q
  have hnorm' (n : ℕ) : ‖q' n‖ ≤ ‖p n‖ :=
    (e.norm_compContinuousMultilinearMap (q n)).le.trans (hnorm n)
  refine ⟨q', hnorm', ?_, FormalMultilinearSeries.radius_le_of_le hnorm', ?_⟩
  · intro n y
    change j (j.equivRange.symm (q n (fun _ => y))) = p n (fun _ => y)
    exact (congrArg Subtype.val (j.equivRange.apply_symm_apply (q n (fun _ => y)))).trans
      (hdiag n y)
  · have h := e.toContinuousLinearMap.comp_hasFPowerSeriesOnBall hq
    change HasFPowerSeriesOnBall
      (fun y => j.equivRange.symm (j.equivRange (f y))) q' x r at h
    simpa only [LinearIsometryEquiv.symm_apply_apply] using h

/-- Pointwise analyticity reflects through a linear isometry with complete source
when the parameter space is discrete c₀. -/
theorem c0_analyticAt_linearIsometry
    (j : W →ₗᵢ[K] Z) {f : C₀(I, K) → W} {x : C₀(I, K)}
    (hf : AnalyticAt K (j ∘ f) x) : AnalyticAt K f x := by
  obtain ⟨p, r, hp⟩ := hf
  obtain ⟨q, _, _, _, hq⟩ := c0_exists_hasFPowerSeriesOnBall_linearIsometry j hp
  exact ⟨q, r, hq⟩

/-- Neighborhood analyticity on any subset of c₀ reflects through the isometry. -/
theorem c0_analyticOnNhd_linearIsometry
    (j : W →ₗᵢ[K] Z) {f : C₀(I, K) → W} {U : Set C₀(I, K)}
    (hf : AnalyticOnNhd K (j ∘ f) U) : AnalyticOnNhd K f U :=
  fun x hx => c0_analyticAt_linearIsometry j (hf x hx)

/-- Analytic reflection on an open c₀ parameter domain. -/
theorem c0_analyticOn_linearIsometry
    (j : W →ₗᵢ[K] Z) {f : C₀(I, K) → W} {U : Set C₀(I, K)}
    (hU : IsOpen U) (hf : AnalyticOn K (j ∘ f) U) : AnalyticOn K f U :=
  hU.analyticOn_iff_analyticOnNhd.mpr
    (c0_analyticOnNhd_linearIsometry j (hU.analyticOn_iff_analyticOnNhd.mp hf))

/-- Reflection is unchanged under any continuous linear equivalence of parameter
spaces with discrete c₀. -/
theorem c0_analyticAt_linearIsometry_of_equiv
    (e : E ≃L[K] C₀(I, K)) (j : W →ₗᵢ[K] Z) {f : E → W} {x : E}
    (hf : AnalyticAt K (j ∘ f) x) : AnalyticAt K f x := by
  have hf' : AnalyticAt K (j ∘ f) (e.symm (e x)) := by
    simpa only [e.symm_apply_apply] using hf
  have hcomp : AnalyticAt K (j ∘ (f ∘ e.symm)) (e x) :=
    hf'.comp (e.symm.analyticAt (e x))
  have h := (c0_analyticAt_linearIsometry j hcomp).comp (e.analyticAt x)
  simpa only [Function.comp_def, e.symm_apply_apply] using h

/-- Neighborhood reflection after a continuous linear change of parameters. -/
theorem c0_analyticOnNhd_linearIsometry_of_equiv
    (e : E ≃L[K] C₀(I, K)) (j : W →ₗᵢ[K] Z) {f : E → W} {U : Set E}
    (hf : AnalyticOnNhd K (j ∘ f) U) : AnalyticOnNhd K f U :=
  fun x hx => c0_analyticAt_linearIsometry_of_equiv e j (hf x hx)

/-- Open-domain reflection after a continuous linear change of parameters. -/
theorem c0_analyticOn_linearIsometry_of_equiv
    (e : E ≃L[K] C₀(I, K)) (j : W →ₗᵢ[K] Z) {f : E → W} {U : Set E}
    (hU : IsOpen U) (hf : AnalyticOn K (j ∘ f) U) : AnalyticOn K f U :=
  hU.analyticOn_iff_analyticOnNhd.mpr
    (c0_analyticOnNhd_linearIsometry_of_equiv e j
      (hU.analyticOn_iff_analyticOnNhd.mp hf))

/-- Reflection for a map defined only on an open subset `U` of c₀, stated for its
zero extension. -/
theorem c0_analyticOn_extend_linearIsometry
    (j : W →ₗᵢ[K] Z) {U : Set C₀(I, K)} (hU : IsOpen U) (f : U → W)
    (hf : AnalyticOn K (j ∘ Function.extend Subtype.val f 0) U) :
    AnalyticOn K (Function.extend Subtype.val f 0) U :=
  c0_analyticOn_linearIsometry j hU hf

/-- Reflection for a map defined only on an open subset of a space isomorphic to c₀. -/
theorem c0_analyticOn_extend_linearIsometry_of_equiv
    (e : E ≃L[K] C₀(I, K)) (j : W →ₗᵢ[K] Z) {U : Set E}
    (hU : IsOpen U) (f : U → W)
    (hf : AnalyticOn K (j ∘ Function.extend Subtype.val f 0) U) :
    AnalyticOn K (Function.extend Subtype.val f 0) U :=
  c0_analyticOn_linearIsometry_of_equiv e j hU hf

end AlternatingAnalytic
