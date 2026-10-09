import AlternatingAnalytic.Analysis.ClosedSubspaceCoefficients
import AlternatingAnalytic.Analysis.FiniteCoordinateLift
import Mathlib.Analysis.Analytic.Within

/-!
# Finite-coordinate analytic reflection

Let `j : F → G` be a closed linear isometry and let the parameter space be boundedly
isomorphic to `K^d`. Then `f` is analytic if and only if `j ∘ f` is (Theorem 4.4).
Neither the field nor the spaces need be complete.
-/

noncomputable section

open scoped Topology NNReal ENNReal

namespace AlternatingAnalytic

variable {K E F G : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup F] [NormedSpace K F]
  [NormedAddCommGroup G] [NormedSpace K G]

/-- Exponentially increasing the coefficient norms preserves a positive radius. -/
theorem radius_pos_of_exponential_bound
    {p : FormalMultilinearSeries K E F} {q : FormalMultilinearSeries K E G}
    (hp : 0 < p.radius) {a : ℝ} (ha : 0 ≤ a)
    (hq : ∀ n, ‖q n‖ ≤ a ^ n * ‖p n‖) : 0 < q.radius := by
  obtain ⟨C, r, hC, hr, hpr⟩ := p.le_mul_pow_of_radius_pos hp
  let b : ℝ := (a + 1) * r
  have hb : 0 < b := mul_pos (by positivity) hr
  let s : ℝ≥0 := ⟨b⁻¹, (inv_pos.mpr hb).le⟩
  have hs : (0 : ℝ≥0∞) < s := by
    exact_mod_cast (inv_pos.mpr hb)
  refine hs.trans_le (q.le_radius_of_bound C fun n => ?_)
  calc
    ‖q n‖ * (s : ℝ) ^ n ≤ (a ^ n * (C * r ^ n)) * (b⁻¹) ^ n := by
      exact mul_le_mul_of_nonneg_right
        ((hq n).trans (mul_le_mul_of_nonneg_left (hpr n) (pow_nonneg ha n)))
        (pow_nonneg (inv_pos.mpr hb).le n)
    _ ≤ ((a + 1) ^ n * (C * r ^ n)) * (b⁻¹) ^ n := by
      gcongr
      linarith
    _ = C := by
      rw [show (a + 1) ^ n * (C * r ^ n) = C * b ^ n by
        dsimp only [b]
        rw [mul_pow]
        ring]
      rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hb.ne', one_pow, mul_one]

/-- A subspace-valued series with the same diagonals and coefficients bounded by
`a ^ n ‖p n‖` makes `f` analytic. -/
theorem analyticAt_of_subspace_series
    (W : Submodule K F) {f : E → W} {x : E}
    {p : FormalMultilinearSeries K E F}
    (hp : HasFPowerSeriesAt (fun y => (f y : F)) p x)
    (q : FormalMultilinearSeries K E W) {a : ℝ} (ha : 0 ≤ a)
    (hq : ∀ n, ‖q n‖ ≤ a ^ n * ‖p n‖)
    (hdiag : ∀ n y, (q n (fun _ => y) : F) = p n (fun _ => y)) :
    AnalyticAt K f x := by
  have hqpos := radius_pos_of_exponential_bound hp.radius_pos ha hq
  obtain ⟨r, hr⟩ := hp
  refine ⟨q, min r q.radius, min_le_right _ _, lt_min hr.r_pos hqpos, ?_⟩
  intro y hy
  have hsum := hr.hasSum (Metric.eball_subset_eball (min_le_left _ _) hy)
  apply (W.subtypeₗᵢ.isEmbedding.isInducing.hasSum_iff
    (g := W.subtypeL) (fun n => q n (fun _ => y)) (f (x + y))).mp
  change HasSum (fun n => (q n (fun _ => y) : F)) (f (x + y) : F)
  simpa only [hdiag] using hsum

/-- On `Fin d → K`, a map into a closed subspace is analytic if it is analytic as a
map into the ambient space. -/
theorem analyticAt_subtype_of_finite_coordinates {d : ℕ}
    (W : Submodule K F) (hW : IsClosed (W : Set F))
    {f : (Fin d → K) → W} {x : Fin d → K}
    (hf : AnalyticAt K (fun y => (f y : F)) x) : AnalyticAt K f x := by
  classical
  obtain ⟨p, hp⟩ := hf
  have hmem (n : ℕ) (y : Fin d → K) : p n (fun _ => y) ∈ W :=
    HasFPowerSeriesAt.diagonal_mem_closedSubspace W hW hp
      (Filter.Eventually.of_forall fun z => (f z).property) n y
  choose q hdiag hnorm using fun n =>
    FiniteCoordinateReflection.exists_lift W (p n) (hmem n)
  exact analyticAt_of_subspace_series W hp q (Nat.cast_nonneg d) hnorm hdiag

/-- On `Fin d → K`, analyticity reflects through a closed linear isometry. -/
theorem analyticAt_of_closed_linearIsometry {d : ℕ}
    (j : F →ₗᵢ[K] G) (hj : IsClosed (Set.range j))
    {f : (Fin d → K) → F} {x : Fin d → K}
    (hf : AnalyticAt K (j ∘ f) x) : AnalyticAt K f x := by
  let g : (Fin d → K) → j.range := fun y => j.equivRange (f y)
  have hg : AnalyticAt K g x :=
    analyticAt_subtype_of_finite_coordinates j.range hj hf
  have h := (j.equivRange.symm.toContinuousLinearEquiv.analyticAt (g x)).comp hg
  change AnalyticAt K (fun y => j.equivRange.symm (j.equivRange (f y))) x at h
  simpa only [LinearIsometryEquiv.symm_apply_apply] using h

/-- Analytic reflection on an open subset of `Fin d → K`. -/
theorem analyticOn_of_closed_linearIsometry {d : ℕ}
    (j : F →ₗᵢ[K] G) (hj : IsClosed (Set.range j))
    {U : Set (Fin d → K)} (hU : IsOpen U) {f : (Fin d → K) → F}
    (hf : AnalyticOn K (j ∘ f) U) : AnalyticOn K f U := by
  apply hU.analyticOn_iff_analyticOnNhd.mpr
  intro x hx
  exact analyticAt_of_closed_linearIsometry j hj
    (hU.analyticOn_iff_analyticOnNhd.mp hf x hx)

/-- Analytic reflection on a space boundedly isomorphic to `Fin d → K` (Theorem 4.4).
The isomorphism is a hypothesis because `K` may be incomplete. -/
theorem analyticAt_of_closed_linearIsometry_of_equiv {d : ℕ}
    (e : E ≃L[K] (Fin d → K)) (j : F →ₗᵢ[K] G) (hj : IsClosed (Set.range j))
    {f : E → F} {x : E} (hf : AnalyticAt K (j ∘ f) x) : AnalyticAt K f x := by
  have hf' : AnalyticAt K (j ∘ f) (e.symm (e x)) := by
    simpa only [e.symm_apply_apply] using hf
  have hcomp : AnalyticAt K (j ∘ (f ∘ e.symm)) (e x) := by
    exact hf'.comp (e.symm.analyticAt (e x))
  have h := (analyticAt_of_closed_linearIsometry j hj hcomp).comp (e.analyticAt x)
  simpa only [Function.comp_def, e.symm_apply_apply] using h

/-- Open-domain reflection with continuous finite coordinates. -/
theorem analyticOn_of_closed_linearIsometry_of_equiv {d : ℕ}
    (e : E ≃L[K] (Fin d → K)) (j : F →ₗᵢ[K] G) (hj : IsClosed (Set.range j))
    {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : AnalyticOn K (j ∘ f) U) : AnalyticOn K f U := by
  apply hU.analyticOn_iff_analyticOnNhd.mpr
  intro x hx
  exact analyticAt_of_closed_linearIsometry_of_equiv e j hj
    (hU.analyticOn_iff_analyticOnNhd.mp hf x hx)

/-- Analytic reflection for `f : U → F`, extended by zero to state `AnalyticOn`. -/
theorem analyticOn_extend_of_closed_linearIsometry {d : ℕ}
    (j : F →ₗᵢ[K] G) (hj : IsClosed (Set.range j))
    {U : Set (Fin d → K)} (hU : IsOpen U) (f : U → F)
    (hf : AnalyticOn K (j ∘ Function.extend Subtype.val f 0) U) :
    AnalyticOn K (Function.extend Subtype.val f 0) U :=
  analyticOn_of_closed_linearIsometry j hj hU hf

end AlternatingAnalytic
