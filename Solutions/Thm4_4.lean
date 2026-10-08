import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import AlternatingAnalytic.Analysis.FiniteCoordinateReflection
import AlternatingAnalytic.Analysis.FiniteCoordinateRadius

/-!
# Theorem 4.4 (finite-coordinate parameters), pp. 10-11

Solution: the statements of `Challenges/Thm4_4.lean`, proved from the library:
* (1): `AlternatingAnalytic.analyticAt_of_closed_linearIsometry_of_equiv`
  (`FiniteCoordinateReflection.lean`); the converse direction is composition with `j`;
* (2): `FiniteCoordinateReflection.exists_lift` (`FiniteCoordinateLift.lean`, the `d^n` bound),
  `AlternatingAnalytic.HasFPowerSeriesAt.diagonal_mem_closedSubspace` (`ClosedSubspaceCoefficients.lean`) and
  `AlternatingAnalytic.radius_pos_of_exponential_bound` (`FiniteCoordinateReflection.lean`),
  assembled as in `analyticAt_subtype_of_finite_coordinates`;
* (3): `AlternatingAnalytic.exists_hasFPowerSeriesOnBall_of_closed_linearIsometry_of_isUltrametricDist`
  (`FiniteCoordinateRadius.lean`).
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
  constructor
  · intro hf x hx
    exact (j.toContinuousLinearMap.analyticAt (f x)).comp (hf x hx)
  · intro hf x hx
    exact AlternatingAnalytic.analyticAt_of_closed_linearIsometry_of_equiv e j hj (hf x hx)

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
  classical
  have hmem : ∀ n (y : Fin d → K), b n (fun _ => y) ∈ j.range := fun n y =>
    AlternatingAnalytic.HasFPowerSeriesAt.diagonal_mem_closedSubspace j.range hj hb
      (Filter.Eventually.of_forall fun z => ⟨f z, rfl⟩) n y
  choose q' hdiag' hnorm' using fun n =>
    FiniteCoordinateReflection.exists_lift j.range (b n) (hmem n)
  let e := j.equivRange.symm.toLinearIsometry
  let q : FormalMultilinearSeries K (Fin d → K) W :=
    e.toContinuousLinearMap.compFormalMultilinearSeries q'
  have hdiag : ∀ n (y : Fin d → K), j (q n (fun _ => y)) = b n (fun _ => y) := by
    intro n y
    change j (j.equivRange.symm (q' n (fun _ => y))) = b n (fun _ => y)
    exact (congrArg Subtype.val (j.equivRange.apply_symm_apply (q' n (fun _ => y)))).trans
      (hdiag' n y)
  have hnorm : ∀ n, ‖q n‖ ≤ (d : ℝ) ^ n * ‖b n‖ := fun n =>
    (e.norm_compContinuousMultilinearMap (q' n)).le.trans (hnorm' n)
  have hqpos := AlternatingAnalytic.radius_pos_of_exponential_bound hb.radius_pos
    (Nat.cast_nonneg d) hnorm
  refine ⟨q, hdiag, ?_, fun n _ => hnorm n⟩
  obtain ⟨r, hr⟩ := hb
  refine ⟨min r q.radius, min_le_right _ _, lt_min hr.r_pos hqpos, fun {y} hy => ?_⟩
  have hsum := hr.hasSum (Metric.eball_subset_eball (min_le_left _ _) hy)
  have hsum' : HasSum (j.toContinuousLinearMap ∘ fun n => q n (fun _ => y))
      (j.toContinuousLinearMap (f (x₀ + y))) := by
    simpa only [Function.comp_def, LinearIsometry.coe_toContinuousLinearMap, hdiag] using hsum
  exact (j.isEmbedding.isInducing.hasSum_iff (g := j.toContinuousLinearMap) _ _).mp hsum'

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
  obtain ⟨r, hr⟩ := hb
  obtain ⟨q, hnorm, hdiag, -, hq⟩ :=
    AlternatingAnalytic.exists_hasFPowerSeriesOnBall_of_closed_linearIsometry_of_isUltrametricDist
      j hj hr
  exact ⟨q, hdiag, hq.hasFPowerSeriesAt, fun n _ => hnorm n⟩

end AlternatingAnalyticChallenge.Thm4_4
