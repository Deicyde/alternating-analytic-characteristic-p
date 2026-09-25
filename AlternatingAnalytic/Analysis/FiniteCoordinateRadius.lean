import AlternatingAnalytic.Analysis.FiniteCoordinateReflection
import Mathlib.Analysis.Normed.Group.Ultra

/-!
# Finite coordinate reflection preserves the coefficient radius

For an ultrametric target, the grouped coordinate coefficients and their lifts
are bounded by the original multilinear coefficient norm. A specified ambient
expansion therefore reflects through a closed linear isometry on its original
ball, with at least its original radius. No completeness is required.
-/

noncomputable section

namespace FiniteCoordinateReflection

open scoped BigOperators

variable {K Z : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup Z] [NormedSpace K Z] [IsUltrametricDist Z] {d n : ℕ}

/-- In an ultrametric target, every grouped coordinate coefficient is bounded by
the norm of the original multilinear map. -/
theorem norm_sumOfType_le_of_isUltrametricDist
    (p : (Fin d → K) [×n]→L[K] Z) (α : Fin d → ℕ) :
    ‖p.toMultilinearMap.sumOfType (fun j => Pi.single j 1) α‖ ≤ ‖p‖ := by
  classical
  unfold MultilinearMap.sumOfType
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg p)
  intro f hf
  apply p.unit_le_opNorm
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro j
  by_cases h : j = f i <;> simp [h]

/-- Grouped coefficients in a subspace of an ultrametric target lift with no
increase in norm. -/
theorem exists_lift_of_sumOfType_mem_of_isUltrametricDist (W : Submodule K Z)
    (p : ContinuousMultilinearMap K (fun _ : Fin n => Fin d → K) Z)
    (hc : ∀ α : Fin d → ℕ,
      p.toMultilinearMap.sumOfType (fun j => Pi.single j 1) α ∈ W) :
    ∃ q : ContinuousMultilinearMap K (fun _ : Fin n => Fin d → K) W,
      (∀ x, (q (fun _ => x) : Z) = p (fun _ => x)) ∧
      ‖q‖ ≤ ‖p‖ := by
  classical
  let T := Set.range (Polarization.selectionType (J := Fin d) (k := n))
  let : Fintype T := (Set.finite_range _).fintype
  let g : (Fin n → Fin d) → T := fun f => ⟨Polarization.selectionType f, f, rfl⟩
  let r : T → Fin n → Fin d := fun t => Classical.choose t.property
  have hr (t : T) : Polarization.selectionType (r t) = t.val :=
    Classical.choose_spec t.property
  let c : T → W := fun t =>
    ⟨p.toMultilinearMap.sumOfType (fun j => Pi.single j 1) t.val, hc t.val⟩
  let q : ContinuousMultilinearMap K (fun _ : Fin n => Fin d → K) W :=
    ∑ t : T, coordinateMonomial (r t) (c t)
  have hfilter (t : T) :
      (Finset.univ.filter (fun f : Fin n → Fin d => g f = t)) =
        Finset.univ.filter (fun f : Fin n → Fin d =>
          Polarization.selectionType f = t.val) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Subtype.ext_iff
  have hprod (t : T) (f : Fin n → Fin d)
      (hf : Polarization.selectionType f = t.val) (x : Fin d → K) :
      (∏ i, x (r t i)) = ∏ i, x (f i) := by
    rw [← Polarization.monomial_selectionMultiIndex,
      ← Polarization.monomial_selectionMultiIndex]
    congr 1
    exact Finsupp.equivFunOnFinite.symm.injective.eq_iff.mpr ((hr t).trans hf.symm)
  refine ⟨q, ?_, ?_⟩
  · intro x
    have hx : (∑ j, x j • Pi.single j (1 : K)) = x := by
      ext j
      simp [← Pi.single_smul]
    calc
      (q (fun _ => x) : Z) = ∑ t : T,
          (∏ i, x (r t i)) • p.toMultilinearMap.sumOfType
            (fun j => Pi.single j 1) t.val := by
        simp [q, c, coordinateMonomial_apply]
      _ = ∑ t : T, ∑ f ∈ Finset.univ.filter (fun f => g f = t),
          (∏ i, x (f i)) • p (fun i => Pi.single (f i) 1) := by
        apply Finset.sum_congr rfl
        intro t _
        rw [hfilter, MultilinearMap.sumOfType, Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro f hf
        rw [hprod t f (Finset.mem_filter.mp hf).2 x]
        rfl
      _ = ∑ f : Fin n → Fin d,
          (∏ i, x (f i)) • p (fun i => Pi.single (f i) 1) :=
        Finset.sum_fiberwise Finset.univ g _
      _ = p (fun _ => x) := by
        conv_rhs => rw [← hx]
        rw [p.map_sum]
        apply Finset.sum_congr rfl
        intro f _
        exact (p.map_smul_univ (fun i => x (f i)) (fun i => Pi.single (f i) 1)).symm
  · apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg p)
    intro m
    simp only [q, sum_apply]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
      (mul_nonneg (norm_nonneg p) (Finset.prod_nonneg fun i _ => norm_nonneg (m i)))
    intro t ht
    calc
      ‖coordinateMonomial (r t) (c t) m‖ ≤
          ‖coordinateMonomial (r t) (c t)‖ * ∏ i, ‖m i‖ :=
        (coordinateMonomial (r t) (c t)).le_opNorm m
      _ ≤ ‖c t‖ * ∏ i, ‖m i‖ := by
        gcongr
        exact norm_coordinateMonomial_le _ _
      _ ≤ ‖p‖ * ∏ i, ‖m i‖ := by
        gcongr
        exact norm_sumOfType_le_of_isUltrametricDist p t.val

/-- A finite-coordinate diagonal in a subspace of an ultrametric target has a
subspace-valued multilinear representative without any increase in norm. -/
theorem exists_lift_of_isUltrametricDist (W : Submodule K Z)
    (p : (Fin d → K) [×n]→L[K] Z)
    (hp : ∀ x, p (fun _ => x) ∈ W) :
    ∃ q : (Fin d → K) [×n]→L[K] W,
      (∀ x, (q (fun _ => x) : Z) = p (fun _ => x)) ∧ ‖q‖ ≤ ‖p‖ :=
  exists_lift_of_sumOfType_mem_of_isUltrametricDist W p (sumOfType_mem W p hp)

end FiniteCoordinateReflection

open scoped Topology NNReal ENNReal

namespace AlternatingAnalytic

variable {K Z W E : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup Z] [NormedSpace K Z]
  [NormedAddCommGroup W] [NormedSpace K W]
  [NormedAddCommGroup E] [NormedSpace K E]

/-- Coefficientwise norm bounds and equal diagonals reflect a represented series
into a subspace on the original ball, without completeness or closedness. -/
theorem hasFPowerSeriesOnBall_subtype_of_diagonal_of_norm_le
    (S : Submodule K Z) {f : E → S} {x : E} {r : ℝ≥0∞}
    {p : FormalMultilinearSeries K E Z}
    (hp : HasFPowerSeriesOnBall (fun y => (f y : Z)) p x r)
    (q : FormalMultilinearSeries K E S)
    (hnorm : ∀ n, ‖q n‖ ≤ ‖p n‖)
    (hdiag : ∀ n y, (q n (fun _ => y) : Z) = p n (fun _ => y)) :
    HasFPowerSeriesOnBall f q x r := by
  refine ⟨hp.r_le.trans (FormalMultilinearSeries.radius_le_of_le hnorm), hp.r_pos, ?_⟩
  intro y hy
  apply (S.subtypeₗᵢ.isEmbedding.isInducing.hasSum_iff
    (g := S.subtypeL) (fun n => q n (fun _ => y)) (f (x + y))).mp
  change HasSum (fun n => (q n (fun _ => y) : Z)) (f (x + y) : Z)
  simpa only [hdiag] using hp.hasSum hy

/-- In finite maximum-norm coordinates, an expansion valued in a closed subspace
of an ultrametric target lifts with no increase in coefficient norms and no loss
of radius. It represents the given map on the original ball. -/
theorem exists_hasFPowerSeriesOnBall_subtype_of_isUltrametricDist
    [IsUltrametricDist Z] {d : ℕ}
    (S : Submodule K Z) (hS : IsClosed (S : Set Z))
    {f : (Fin d → K) → S} {x : Fin d → K} {r : ℝ≥0∞}
    {p : FormalMultilinearSeries K (Fin d → K) Z}
    (hp : HasFPowerSeriesOnBall (fun y => (f y : Z)) p x r) :
    ∃ q : FormalMultilinearSeries K (Fin d → K) S,
      (∀ n, ‖q n‖ ≤ ‖p n‖) ∧
      (∀ n y, (q n (fun _ => y) : Z) = p n (fun _ => y)) ∧
      p.radius ≤ q.radius ∧ HasFPowerSeriesOnBall f q x r := by
  classical
  have hmem (n : ℕ) (y : Fin d → K) : p n (fun _ => y) ∈ S :=
    HasFPowerSeriesAt.diagonal_mem_closedSubspace S hS hp.hasFPowerSeriesAt
      (Filter.Eventually.of_forall fun z => (f z).property) n y
  choose q hdiag hnorm using fun n =>
    FiniteCoordinateReflection.exists_lift_of_isUltrametricDist S (p n) (hmem n)
  exact ⟨q, hnorm, hdiag, FormalMultilinearSeries.radius_le_of_le hnorm,
    hasFPowerSeriesOnBall_subtype_of_diagonal_of_norm_le S hp q hnorm hdiag⟩

/-- Finite coordinate reflection through a closed linear isometry into an
ultrametric target preserves the coefficient bounds and the original ball of a
specified expansion, without completeness assumptions on the field or spaces. -/
theorem exists_hasFPowerSeriesOnBall_of_closed_linearIsometry_of_isUltrametricDist
    [IsUltrametricDist Z] {d : ℕ}
    (j : W →ₗᵢ[K] Z) (hj : IsClosed (Set.range j))
    {f : (Fin d → K) → W} {x : Fin d → K} {r : ℝ≥0∞}
    {p : FormalMultilinearSeries K (Fin d → K) Z}
    (hp : HasFPowerSeriesOnBall (j ∘ f) p x r) :
    ∃ q : FormalMultilinearSeries K (Fin d → K) W,
      (∀ n, ‖q n‖ ≤ ‖p n‖) ∧
      (∀ n y, j (q n (fun _ => y)) = p n (fun _ => y)) ∧
      p.radius ≤ q.radius ∧ HasFPowerSeriesOnBall f q x r := by
  let g : (Fin d → K) → j.range := fun y => j.equivRange (f y)
  obtain ⟨q, hnorm, hdiag, _, hq⟩ :=
    exists_hasFPowerSeriesOnBall_subtype_of_isUltrametricDist j.range hj (f := g) hp
  let e := j.equivRange.symm.toLinearIsometry
  let q' := e.toContinuousLinearMap.compFormalMultilinearSeries q
  have hnorm' (n : ℕ) : ‖q' n‖ ≤ ‖p n‖ := by
    exact (e.norm_compContinuousMultilinearMap (q n)).le.trans (hnorm n)
  refine ⟨q', hnorm', ?_, FormalMultilinearSeries.radius_le_of_le hnorm', ?_⟩
  · intro n y
    change j (j.equivRange.symm (q n (fun _ => y))) = p n (fun _ => y)
    exact (congrArg Subtype.val (j.equivRange.apply_symm_apply (q n (fun _ => y)))).trans
      (hdiag n y)
  · have h := e.toContinuousLinearMap.comp_hasFPowerSeriesOnBall hq
    change HasFPowerSeriesOnBall
      (fun y => j.equivRange.symm (j.equivRange (f y))) q' x r at h
    simpa only [LinearIsometryEquiv.symm_apply_apply] using h

/-- The full finite-coordinate radius preservation statement for a closed subspace:
every grouped coefficient satisfies the sharp bound, and a single lifted series
has the same diagonals, no larger coefficient norms, at least the ambient radius,
and represents the given map on the original ball. -/
theorem finite_coordinate_radius_preservation_full_subtype
    [IsUltrametricDist Z] {d : ℕ}
    (S : Submodule K Z) (hS : IsClosed (S : Set Z))
    {f : (Fin d → K) → S} {x : Fin d → K} {r : ℝ≥0∞}
    {p : FormalMultilinearSeries K (Fin d → K) Z}
    (hp : HasFPowerSeriesOnBall (fun y => (f y : Z)) p x r) :
    ∃ q : FormalMultilinearSeries K (Fin d → K) S,
      (∀ n (α : Fin d → ℕ),
        ‖(p n).toMultilinearMap.sumOfType (fun j => Pi.single j 1) α‖ ≤ ‖p n‖) ∧
      (∀ n, ‖q n‖ ≤ ‖p n‖) ∧
      (∀ n y, (q n (fun _ => y) : Z) = p n (fun _ => y)) ∧
      p.radius ≤ q.radius ∧ HasFPowerSeriesOnBall f q x r := by
  obtain ⟨q, hq⟩ := exists_hasFPowerSeriesOnBall_subtype_of_isUltrametricDist S hS hp
  exact ⟨q, fun n α =>
    FiniteCoordinateReflection.norm_sumOfType_le_of_isUltrametricDist (p n) α, hq⟩

/-- The full finite-coordinate radius preservation statement through a closed
linear isometry into an ultrametric target, including both the grouped coefficient
bounds and all bounds, identities, and convergence properties of one reflected
series. The dimension, degree, and original radius are unrestricted. -/
theorem finite_coordinate_radius_preservation_full
    [IsUltrametricDist Z] {d : ℕ}
    (j : W →ₗᵢ[K] Z) (hj : IsClosed (Set.range j))
    {f : (Fin d → K) → W} {x : Fin d → K} {r : ℝ≥0∞}
    {p : FormalMultilinearSeries K (Fin d → K) Z}
    (hp : HasFPowerSeriesOnBall (j ∘ f) p x r) :
    ∃ q : FormalMultilinearSeries K (Fin d → K) W,
      (∀ n (α : Fin d → ℕ),
        ‖(p n).toMultilinearMap.sumOfType (fun j => Pi.single j 1) α‖ ≤ ‖p n‖) ∧
      (∀ n, ‖q n‖ ≤ ‖p n‖) ∧
      (∀ n y, j (q n (fun _ => y)) = p n (fun _ => y)) ∧
      p.radius ≤ q.radius ∧ HasFPowerSeriesOnBall f q x r := by
  obtain ⟨q, hq⟩ :=
    exists_hasFPowerSeriesOnBall_of_closed_linearIsometry_of_isUltrametricDist j hj hp
  exact ⟨q, fun n α =>
    FiniteCoordinateReflection.norm_sumOfType_le_of_isUltrametricDist (p n) α, hq⟩

end AlternatingAnalytic
