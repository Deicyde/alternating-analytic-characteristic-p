import AlternatingAnalytic.Analysis.TensorTestFamily
import AlternatingAnalytic.Analysis.FiniteCoordinateReflection
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Order.Filter.AtTopBot.Finset

/-!
# Universal analytic reflection and exponential tensor projections

The analytic tensor criterion `fam:thm:tensor-analytic`, for ordinary separated
completed projective tensor powers over a complete nontrivially normed field.
-/

noncomputable section

open Filter
open scoped Topology NNReal ENNReal BigOperators

namespace AlternatingAnalytic

universe u v

/-- A finite extended root-limsup is equivalent to a uniform exponential bound;
the finitely many initial exceptions are absorbed into the same constant. -/
theorem root_limsup_lt_top_iff_exponential_bound (s : ℕ → ℝ≥0) :
    Filter.limsup
      (fun m : ℕ => (s m : ℝ≥0∞) ^ (((m + 1 : ℕ) : ℝ)⁻¹))
      Filter.atTop < ⊤ ↔
    ∃ A : ℝ, 1 ≤ A ∧ ∀ m, (s m : ℝ) ≤ A ^ (m + 1) := by
  constructor
  · intro h
    obtain ⟨B, hB, _⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
    have he := Filter.eventually_lt_of_limsup_lt hB
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp he
    let A : ℝ≥0 := max 1 (max B (∑ i ∈ Finset.range N, s i))
    have hA : 1 ≤ A := le_max_left _ _
    refine ⟨A, by exact_mod_cast hA, fun m => ?_⟩
    have hm : s m ≤ A ^ (m + 1) := by
      by_cases hn : N ≤ m
      · have hroot := (hN m hn).le
        have hpow := (ENNReal.rpow_inv_le_iff (by positivity : (0 : ℝ) < (m + 1 : ℕ))).mp hroot
        rw [ENNReal.rpow_natCast] at hpow
        have hsmall : s m ≤ B ^ (m + 1) := by exact_mod_cast hpow
        exact hsmall.trans (pow_le_pow_left' ((le_max_left _ _).trans (le_max_right _ _)) _)
      · have hsmall : s m ≤ ∑ i ∈ Finset.range N, s i := by
          exact Finset.single_le_sum (fun i _ => by positivity) (Finset.mem_range.mpr (by omega))
        exact hsmall.trans (((le_max_right _ _).trans (le_max_right _ _)).trans
          (le_self_pow₀ hA (Nat.succ_ne_zero m)))
    exact_mod_cast hm
  · rintro ⟨A, hA, hs⟩
    let B : ℝ≥0 := ⟨A, by linarith⟩
    apply lt_of_le_of_lt (b := (B : ℝ≥0∞))
    · apply Filter.limsup_le_of_le (by isBoundedDefault)
      apply Filter.Eventually.of_forall
      intro m
      apply (ENNReal.rpow_inv_le_iff (by positivity : (0 : ℝ) < (m + 1 : ℕ))).mpr
      rw [ENNReal.rpow_natCast]
      have hm : s m ≤ B ^ (m + 1) := by exact_mod_cast hs m
      exact_mod_cast hm
    · exact ENNReal.coe_lt_top

/-- A coefficient estimate with a constant factor gives a uniform bound in every
positive degree. -/
theorem exponential_bound_of_mul_pow_bound (s : ℕ → ℝ)
    {C r : ℝ} (_hC : 0 < C) (hr : 0 < r)
    (hs : ∀ m, s m ≤ C * r ^ (m + 1)) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ m, s m ≤ A ^ (m + 1) := by
  let c : ℝ := max 1 C
  let t : ℝ := max 1 r
  have hc : 1 ≤ c := le_max_left _ _
  have ht : 1 ≤ t := le_max_left _ _
  refine ⟨c * t, one_le_mul_of_one_le_of_one_le hc ht, fun m => ?_⟩
  calc
    s m ≤ C * r ^ (m + 1) := hs m
    _ ≤ c ^ (m + 1) * t ^ (m + 1) := by
      apply mul_le_mul
      · exact (le_max_right _ _).trans (le_self_pow₀ hc (Nat.succ_ne_zero m))
      · exact pow_le_pow_left₀ hr.le (le_max_right _ _) _
      · positivity
      · positivity
    _ = (c * t) ^ (m + 1) := (mul_pow _ _ _).symm

variable (K P : Type u) [NontriviallyNormedField K] [CompleteSpace K]
  [NormedAddCommGroup P] [NormedSpace K P] [CompleteSpace P]

/-- Universal analytic reflection through closed subspaces of Banach targets.
The target universe contains the actual dependent c₀ tensor test space.

We use total maps on `P` to express analyticity on an open set `U`. This is equivalent
to the source's maps `U → W`: extend such a map by zero outside `U`, and restrict a
total map to `U`. Analyticity is local on `U`, so the exterior values have no effect.
-/
def UniversalAnalyticReflection : Prop :=
  ∀ (Z : Type u) [NormedAddCommGroup Z] [NormedSpace K Z] [CompleteSpace Z],
    ∀ (W : Submodule K Z), IsClosed (W : Set Z) →
    ∀ (U : Set P), IsOpen U → ∀ f : P → W,
      AnalyticOnNhd K (fun x => (f x : Z)) U → AnalyticOnNhd K f U

variable {K P}

omit [CompleteSpace K] [CompleteSpace P] in
/-- Universal reflection applied to a map defined only on its open domain. -/
theorem UniversalAnalyticReflection.analyticOnNhd_extend
    (h : UniversalAnalyticReflection K P)
    {Z : Type u} [NormedAddCommGroup Z] [NormedSpace K Z] [CompleteSpace Z]
    (W : Submodule K Z) (hW : IsClosed (W : Set Z))
    {U : Set P} (hU : IsOpen U) (f : U → W)
    (hf : AnalyticOnNhd K (W.subtypeL ∘ Function.extend Subtype.val f 0) U) :
    AnalyticOnNhd K (Function.extend Subtype.val f 0) U :=
  h Z W hW U hU _ hf

omit [CompleteSpace K] [CompleteSpace P] in
/-- The source's open-domain formulation, expressed by zero extension. -/
theorem UniversalAnalyticReflection.analyticOn_extend
    (h : UniversalAnalyticReflection K P)
    {Z : Type u} [NormedAddCommGroup Z] [NormedSpace K Z] [CompleteSpace Z]
    (W : Submodule K Z) (hW : IsClosed (W : Set Z))
    {U : Set P} (hU : IsOpen U) (f : U → W)
    (hf : AnalyticOn K (W.subtypeL ∘ Function.extend Subtype.val f 0) U) :
    AnalyticOn K (Function.extend Subtype.val f 0) U :=
  hU.analyticOn_iff_analyticOnNhd.mpr
    (h.analyticOnNhd_extend W hW hU f (hU.analyticOn_iff_analyticOnNhd.mp hf))

omit [CompleteSpace K] [CompleteSpace P] in
/-- The degree-zero coefficient restricts directly to the subspace, preserving its
original norm bound. No degree-zero tensor projection is needed. -/
theorem exists_zero_subspace_coefficient
    {Z : Type v} [NormedAddCommGroup Z] [NormedSpace K Z]
    (W : Submodule K Z)
    (B : ContinuousMultilinearMap K (fun _ : Fin 0 => P) Z)
    (hB : ∀ x, B (fun _ => x) ∈ W) :
    ∃ C : ContinuousMultilinearMap K (fun _ : Fin 0 => P) W,
      (∀ x, (C (fun _ => x) : Z) = B (fun _ => x)) ∧ ‖C‖ ≤ ‖B‖ := by
  have hmem (v : Fin 0 → P) : B v ∈ W := by
    have hv : v = fun _ => (0 : P) := Subsingleton.elim _ _
    rw [hv]
    exact hB 0
  refine ⟨B.codRestrict W hmem, fun _ => rfl, ?_⟩
  exact ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg B) (fun v => B.le_opNorm v)

/-- Exponentially bounded tensor projections reflect every ambient analytic germ
with values in a closed subspace. The target may lie in any universe. -/
theorem analyticAt_subtype_of_tensor_projections
    (R : ∀ m : ℕ, TensorPower K P (m + 1) →L[K] DiagonalSpan K P (m + 1))
    (hR : ∀ m, (R m).comp (DiagonalSpan K P (m + 1)).subtypeL =
      ContinuousLinearMap.id K (DiagonalSpan K P (m + 1)))
    {A : ℝ} (hA : 1 ≤ A) (hbound : ∀ m, ‖R m‖ ≤ A ^ (m + 1))
    {Z : Type v} [NormedAddCommGroup Z] [NormedSpace K Z] [CompleteSpace Z]
    (W : Submodule K Z) (hW : IsClosed (W : Set Z))
    {f : P → W} {x : P} (hf : AnalyticAt K (fun y => (f y : Z)) x) :
    AnalyticAt K f x := by
  classical
  obtain ⟨p, hp⟩ := hf
  have hmem (n : ℕ) (y : P) : p n (fun _ => y) ∈ W :=
    HasFPowerSeriesAt.diagonal_mem_closedSubspace W hW hp
      (Filter.Eventually.of_forall fun z => (f z).property) n y
  have hcoeff (n : ℕ) :
      ∃ C : ContinuousMultilinearMap K (fun _ : Fin n => P) W,
        (∀ y, (C (fun _ => y) : Z) = p n (fun _ => y)) ∧
          ‖C‖ ≤ A ^ n * ‖p n‖ := by
    cases n with
    | zero =>
      simpa only [pow_zero, one_mul] using
        exists_zero_subspace_coefficient W (p 0) (hmem 0)
    | succ m =>
      obtain ⟨C, hdiag, hnorm⟩ := exists_diagonal_lift_of_projection (m + 1)
        (R m) (hR m) W hW (p (m + 1)) (hmem (m + 1))
      refine ⟨C, hdiag, hnorm.trans ?_⟩
      calc
        ‖p (m + 1)‖ * ‖R m‖ ≤ ‖p (m + 1)‖ * A ^ (m + 1) :=
          mul_le_mul_of_nonneg_left (hbound m) (norm_nonneg _)
        _ = A ^ (m + 1) * ‖p (m + 1)‖ := mul_comm _ _
  choose q hdiag hnorm using hcoeff
  exact analyticAt_of_subspace_series W hp q (zero_le_one.trans hA) hnorm hdiag

/-- Sufficiency of a single uniformly exponentially bounded projection family. -/
theorem universal_analytic_reflection_of_tensor_projections
    (R : ∀ m : ℕ, TensorPower K P (m + 1) →L[K] DiagonalSpan K P (m + 1))
    (hR : ∀ m, (R m).comp (DiagonalSpan K P (m + 1)).subtypeL =
      ContinuousLinearMap.id K (DiagonalSpan K P (m + 1)))
    {A : ℝ} (hA : 1 ≤ A) (hbound : ∀ m, ‖R m‖ ≤ A ^ (m + 1)) :
    UniversalAnalyticReflection K P := by
  intro Z _ _ _ W hW U _ f hf x hx
  exact analyticAt_subtype_of_tensor_projections R hR hA hbound W hW (hf x hx)

section TensorTest

omit [CompleteSpace K] [CompleteSpace P]

/-- The coefficient coordinate of an expansion of the reflected tensor test map
has the prescribed diagonal. This uses diagonal uniqueness only. -/
theorem tensorTest_expansion_deltaCoordinate
    {q : FormalMultilinearSeries K P (tensorTestSubmodule (K := K) (P := P))}
    (hq : HasFPowerSeriesAt (tensorTestMap (K := K) (P := P)) q 0)
    (m : ℕ) (x : P) :
    (tensorTestDeltaCoordinate m (q (m + 1) (fun _ => x)) : TensorPower K P (m + 1)) =
      diagonalTensor (K := K) (m + 1) x := by
  let j := (tensorTestSubmodule (K := K) (P := P)).subtypeL
  have hjq : HasFPowerSeriesAt
      (fun x : P => (tensorTestMap (K := K) x : tensorTestSpace K P))
      (j.compFormalMultilinearSeries q) 0 := by
    obtain ⟨r, hr⟩ := hq
    exact ⟨r, j.comp_hasFPowerSeriesOnBall hr⟩
  have ha : HasFPowerSeriesAt
      (fun x : P => (tensorTestMap (K := K) x : tensorTestSpace K P))
      tensorTestSeries 0 := ⟨1, tensorTestMap_hasFPowerSeriesOnBall⟩
  have hz : HasFPowerSeriesAt (0 : P → tensorTestSpace K P)
      (j.compFormalMultilinearSeries q - tensorTestSeries) 0 := by
    simpa only [sub_self] using hjq.sub ha
  have hd := hz.apply_eq_zero (m + 1) x
  have he : j (q (m + 1) (fun _ => x)) =
      tensorTestSeries (K := K) (m + 1) (fun _ => x) := by
    exact sub_eq_zero.mp hd
  simpa only [tensorTestDeltaCoordinate_coe, j, Submodule.subtypeL_apply,
    tensorTestSeries_coordinate, diagonalTensor] using congrArg (tensorTestCoordinate m) he

/-- The actual tensor linearization of the selected coordinate of one reflected
series coefficient. -/
def tensorTestProjection
    (q : FormalMultilinearSeries K P (tensorTestSubmodule (K := K) (P := P))) (m : ℕ) :
    TensorPower K P (m + 1) →L[K] DiagonalSpan K P (m + 1) :=
  completedProjectiveTensorLiftIsometry (fun _ : Fin (m + 1) => P)
    (DiagonalSpan K P (m + 1))
    ((tensorTestDeltaCoordinate m).compContinuousMultilinearMap (q (m + 1)))

theorem tensorTestProjection_retraction
    {q : FormalMultilinearSeries K P (tensorTestSubmodule (K := K) (P := P))}
    (hq : HasFPowerSeriesAt (tensorTestMap (K := K) (P := P)) q 0) (m : ℕ) :
    (tensorTestProjection q m).comp (DiagonalSpan K P (m + 1)).subtypeL =
      ContinuousLinearMap.id K (DiagonalSpan K P (m + 1)) := by
  apply retraction_of_fixes_diagonalTensor
  intro x
  simpa only [tensorTestProjection, diagonalTensor,
    completedProjectiveTensorLiftIsometry_tprod,
    ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply] using
      tensorTest_expansion_deltaCoordinate hq m x

theorem norm_tensorTestProjection_le
    (q : FormalMultilinearSeries K P (tensorTestSubmodule (K := K) (P := P))) (m : ℕ) :
    ‖tensorTestProjection q m‖ ≤ ‖q (m + 1)‖ := by
  calc
    ‖tensorTestProjection q m‖ =
        ‖(tensorTestDeltaCoordinate m).compContinuousMultilinearMap (q (m + 1))‖ :=
      norm_completedProjectiveTensorLiftIsometry _ _
    _ ≤ ‖tensorTestDeltaCoordinate (K := K) (P := P) m‖ * ‖q (m + 1)‖ :=
      ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ ≤ 1 * ‖q (m + 1)‖ := mul_le_mul_of_nonneg_right
      (norm_tensorTestDeltaCoordinate_le m) (norm_nonneg _)
    _ = ‖q (m + 1)‖ := one_mul _

/-- A reflected analytic test germ produces one projection family with a common
exponential coefficient bound, retaining the quantitative linearization estimate. -/
theorem tensor_projections_of_analyticAt_tensorTestMap
    (h : AnalyticAt K (tensorTestMap (K := K) (P := P)) 0) :
    ∃ R : ∀ m : ℕ, TensorPower K P (m + 1) →L[K] DiagonalSpan K P (m + 1),
      (∀ m, (R m).comp (DiagonalSpan K P (m + 1)).subtypeL =
        ContinuousLinearMap.id K (DiagonalSpan K P (m + 1))) ∧
      ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ ∀ m, ‖R m‖ ≤ C * r ^ (m + 1) := by
  obtain ⟨q, hq⟩ := h
  obtain ⟨C, r, hC, hr, hbound⟩ := q.le_mul_pow_of_radius_pos hq.radius_pos
  refine ⟨tensorTestProjection q, tensorTestProjection_retraction hq, C, r, hC, hr, ?_⟩
  intro m
  exact (norm_tensorTestProjection_le q m).trans (hbound (m + 1))

end TensorTest

omit [CompleteSpace K] [CompleteSpace P] in
/-- Necessity retains a common coefficient bound for the same family of projections
obtained by linearizing the reflected dependent c₀ tensor test series. -/
theorem tensor_projections_of_universal_analytic_reflection
    (h : UniversalAnalyticReflection K P) :
    ∃ R : ∀ m : ℕ, TensorPower K P (m + 1) →L[K] DiagonalSpan K P (m + 1),
      (∀ m, (R m).comp (DiagonalSpan K P (m + 1)).subtypeL =
        ContinuousLinearMap.id K (DiagonalSpan K P (m + 1))) ∧
      ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ ∀ m, ‖R m‖ ≤ C * r ^ (m + 1) := by
  apply tensor_projections_of_analyticAt_tensorTestMap
  exact h (tensorTestSpace K P) tensorTestSubmodule isClosed_tensorTestSubmodule
    (Metric.ball 0 1) Metric.isOpen_ball tensorTestMap tensorTestMap_analyticOnNhd
    0 (by simp)

omit [CompleteSpace K] [CompleteSpace P] in
/-- For one fixed projection family, the paper's extended root-limsup condition is
equivalent to a uniform exponential norm bound in every positive degree. -/
theorem tensor_projections_root_limsup_iff
    (R : ∀ m : ℕ, TensorPower K P (m + 1) →L[K] DiagonalSpan K P (m + 1)) :
    Filter.limsup
      (fun m : ℕ => (‖R m‖₊ : ℝ≥0∞) ^ (((m + 1 : ℕ) : ℝ)⁻¹))
      Filter.atTop < ⊤ ↔
    ∃ A : ℝ, 1 ≤ A ∧ ∀ m, ‖R m‖ ≤ A ^ (m + 1) :=
  root_limsup_lt_top_iff_exponential_bound (fun m => ‖R m‖₊)

/-- The uniform-exponential-bound form of the analytic tensor criterion. -/
theorem universal_analytic_reflection_iff_exponential_tensor_projections :
    UniversalAnalyticReflection K P ↔
      ∃ R : ∀ m : ℕ, TensorPower K P (m + 1) →L[K] DiagonalSpan K P (m + 1),
        (∀ m, (R m).comp (DiagonalSpan K P (m + 1)).subtypeL =
          ContinuousLinearMap.id K (DiagonalSpan K P (m + 1))) ∧
        ∃ A : ℝ, 1 ≤ A ∧ ∀ m, ‖R m‖ ≤ A ^ (m + 1) := by
  constructor
  · intro h
    obtain ⟨R, hR, C, r, hC, hr, hbound⟩ :=
      tensor_projections_of_universal_analytic_reflection h
    exact ⟨R, hR, exponential_bound_of_mul_pow_bound (fun m => ‖R m‖) hC hr hbound⟩
  · rintro ⟨R, hR, A, hA, hbound⟩
    exact universal_analytic_reflection_of_tensor_projections R hR hA hbound

/-- The full analytic tensor criterion: universal reflection holds exactly when the
actual positive-degree diagonal spans have a single family of bounded projections
whose norm roots have finite extended limsup. -/
theorem universal_analytic_reflection_iff_tensor_projections :
    UniversalAnalyticReflection K P ↔
      ∃ R : ∀ m : ℕ, TensorPower K P (m + 1) →L[K] DiagonalSpan K P (m + 1),
        (∀ m, (R m).comp (DiagonalSpan K P (m + 1)).subtypeL =
          ContinuousLinearMap.id K (DiagonalSpan K P (m + 1))) ∧
        Filter.limsup
          (fun m : ℕ => (‖R m‖₊ : ℝ≥0∞) ^ (((m + 1 : ℕ) : ℝ)⁻¹))
          Filter.atTop < ⊤ := by
  rw [universal_analytic_reflection_iff_exponential_tensor_projections]
  simp only [tensor_projections_root_limsup_iff]

end AlternatingAnalytic
