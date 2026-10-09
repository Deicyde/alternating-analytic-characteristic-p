import AlternatingAnalytic.Analysis.TensorTestFamily
import AlternatingAnalytic.Analysis.FiniteCoordinateReflection
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Order.Filter.AtTopBot.Finset

/-!
# Universal analytic reflection and exponential tensor projections

Theorem G.3: a Banach space `P` has universal analytic reflection if and only if there are
projections `R_n : T_n(P) → Δ_n(P)` with `limsup ‖R_n‖^{1/n} < ∞`. Here `T_n(P)` is the
completed projective tensor power and `Δ_n(P)` the closed span of the pure powers `x^{⊗n}`.
The "if" direction replaces each ambient coefficient by a `W`-valued one using `R_n`; the
"only if" direction applies reflection to the tensor test map of `TensorTestFamily.lean`.
-/

noncomputable section

open Filter
open scoped Topology NNReal ENNReal BigOperators

namespace AlternatingAnalytic

universe u v

/-- `limsup s_m^{1/(m+1)} < ∞` in `ℝ≥0∞` if and only if `s_m ≤ A^(m+1)` for some
`A ≥ 1` and all `m`. -/
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

/-- A bound `s_m ≤ C r^(m+1)` with `C, r > 0` gives a bound `s_m ≤ A^(m+1)` for some
`A ≥ 1`. -/
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

/-- `P` has universal analytic reflection: for every closed subspace `W` of a Banach space
`Z` in `Type u`, a map into `W` that is analytic into `Z` on an open set is analytic into `W`.

Maps are total on `P`; a map `U → W` corresponds to its extension by zero, and analyticity
on the open set `U` does not see values outside `U`. -/
def UniversalAnalyticReflection : Prop :=
  ∀ (Z : Type u) [NormedAddCommGroup Z] [NormedSpace K Z] [CompleteSpace Z],
    ∀ (W : Submodule K Z), IsClosed (W : Set Z) →
    ∀ (U : Set P), IsOpen U → ∀ f : P → W,
      AnalyticOnNhd K (fun x => (f x : Z)) U → AnalyticOnNhd K f U

variable {K P}

omit [CompleteSpace K] [CompleteSpace P] in
/-- Universal reflection for a map defined on an open set, extended by zero. -/
theorem UniversalAnalyticReflection.analyticOnNhd_extend
    (h : UniversalAnalyticReflection K P)
    {Z : Type u} [NormedAddCommGroup Z] [NormedSpace K Z] [CompleteSpace Z]
    (W : Submodule K Z) (hW : IsClosed (W : Set Z))
    {U : Set P} (hU : IsOpen U) (f : U → W)
    (hf : AnalyticOnNhd K (W.subtypeL ∘ Function.extend Subtype.val f 0) U) :
    AnalyticOnNhd K (Function.extend Subtype.val f 0) U :=
  h Z W hW U hU _ hf

omit [CompleteSpace K] [CompleteSpace P] in
/-- The same, with `AnalyticOn` on the open set. -/
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
/-- A degree-zero coefficient with values in `W` restricts to `W` with the same norm
bound. -/
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

/-- Exponentially bounded tensor projections reflect analyticity at a point into any closed
subspace. The target may lie in any universe. -/
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

/-- The "if" direction of Theorem G.3, for projections with a bound `‖R_n‖ ≤ A^n`
in every degree `n ≥ 1`. -/
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

/-- For a `W`-valued expansion `q` of the tensor test map, `π_n q_n (x, …, x) = x^{⊗n}`. -/
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

/-- The projection `T_n(P) → Δ_n(P)` obtained by linearizing `π_n q_n`. -/
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

/-- If the tensor test map is analytic into `W` at zero, there are projections `R_n` with
`‖R_n‖ ≤ C r^n`. -/
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
/-- The "only if" direction of Theorem G.3: reflecting the tensor test map gives
projections with `‖R_n‖ ≤ C r^n`. -/
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
/-- For a family of projections, `limsup ‖R_n‖^{1/n} < ∞` is equivalent to a bound
`‖R_n‖ ≤ A^n`. -/
theorem tensor_projections_root_limsup_iff
    (R : ∀ m : ℕ, TensorPower K P (m + 1) →L[K] DiagonalSpan K P (m + 1)) :
    Filter.limsup
      (fun m : ℕ => (‖R m‖₊ : ℝ≥0∞) ^ (((m + 1 : ℕ) : ℝ)⁻¹))
      Filter.atTop < ⊤ ↔
    ∃ A : ℝ, 1 ≤ A ∧ ∀ m, ‖R m‖ ≤ A ^ (m + 1) :=
  root_limsup_lt_top_iff_exponential_bound (fun m => ‖R m‖₊)

/-- Theorem G.3, with the condition stated as a bound `‖R_n‖ ≤ A^n`. -/
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

/-- Theorem G.3: universal analytic reflection holds if and only if there are projections
`R_n : T_n(P) → Δ_n(P)`, `n ≥ 1`, with `limsup ‖R_n‖^{1/n} < ∞`; the limsup is taken
in `ℝ≥0∞`. -/
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
