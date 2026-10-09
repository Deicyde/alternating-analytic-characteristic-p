import AlternatingAnalytic.Analysis.LaurentField
import AlternatingAnalytic.Analysis.ProjectiveExterior
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Diagonal transitions over a `c₀` base (Corollary C.7)

Let `K` be a complete nontrivially normed field and `E = ℓ^∞(ℕ, K)`. For `a` in the open unit
ball of `c₀(ℕ, K)`, the transition `D_{1+a} ∈ L(E, E)` (coordinatewise multiplication by `1 + a`)
is a unit of `L(E, E)`, since `D_{1+a} = 1 + D_a` and `‖D_a‖ ≤ ‖a‖ < 1`; it is an isometry when `K`
is ultrametric, since then `‖1 + a_i‖ = 1`. The map `a ↦ D_{1+a}` is affine, hence analytic, and
`a ↦ D_{1+a}⁻¹` is analytic on the ball because inversion is analytic on the units of the Banach
algebra `L(E, E)`. Finally `W ∘ (D_{1+a}, …, D_{1+a}) = A(id + D_a)(W)`, so the non-analyticity of
the induced section is the second assertion of Proposition C.6 at `u₀ = id`, taken here as a
hypothesis.
-/

set_option backward.isDefEq.respectTransparency false

open scoped NNReal BoundedContinuousFunction ZeroAtInfty

namespace AlternatingAnalytic.DiagonalTransitions

universe u v

variable {K : Type u} [NontriviallyNormedField K]

/-- The inclusion `c₀(ℕ, K) → ℓ^∞(ℕ, K)` as a continuous linear map. -/
noncomputable def toBCFCLM (K : Type u) [NontriviallyNormedField K] :
    C₀(ℕ, K) →L[K] (ℕ →ᵇ K) where
  toFun := ZeroAtInftyContinuousMap.toBCF
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := ZeroAtInftyContinuousMap.isometry_toBCF.continuous

/-- `D_{1+a} = 1 + D_a` in `L(E, E)`. -/
theorem mul_one_add (a : C₀(ℕ, K)) :
    ContinuousLinearMap.mul K (ℕ →ᵇ K) (1 + a.toBCF) =
      1 + ContinuousLinearMap.mul K (ℕ →ᵇ K) a.toBCF := by
  ext z i
  simp

/-- `‖D_a‖ ≤ ‖a‖` for `a ∈ c₀(ℕ, K)`. -/
theorem norm_mul_toBCF_le (a : C₀(ℕ, K)) :
    ‖ContinuousLinearMap.mul K (ℕ →ᵇ K) a.toBCF‖ ≤ ‖a‖ :=
  (ContinuousLinearMap.opNorm_mul_apply_le K _ _).trans_eq
    ZeroAtInftyContinuousMap.norm_toBCF_eq_norm

/-- On the open unit ball of `c₀(ℕ, K)`, `D_{1+a}` is a unit of `L(E, E)`. -/
theorem isUnit_mul_one_add [CompleteSpace K] {a : C₀(ℕ, K)}
    (ha : a ∈ Metric.ball (0 : C₀(ℕ, K)) 1) :
    IsUnit (ContinuousLinearMap.mul K (ℕ →ᵇ K) (1 + a.toBCF)) := by
  have h : ‖-ContinuousLinearMap.mul K (ℕ →ᵇ K) a.toBCF‖ < 1 := by
    rw [norm_neg]
    exact (norm_mul_toBCF_le a).trans_lt (mem_ball_zero_iff.mp ha)
  refine ⟨Units.oneSub _ h, ?_⟩
  rw [mul_one_add]
  simp [Units.oneSub, sub_eq_add_neg]

/-- Over an ultrametric field, `D_{1+a}` is an isometry for `a` in the open unit ball. -/
theorem norm_mul_one_add_apply [IsUltrametricDist K] {a : C₀(ℕ, K)}
    (ha : a ∈ Metric.ball (0 : C₀(ℕ, K)) 1) (z : ℕ →ᵇ K) :
    ‖ContinuousLinearMap.mul K (ℕ →ᵇ K) (1 + a.toBCF) z‖ = ‖z‖ := by
  have hpt : ∀ i, ‖(ContinuousLinearMap.mul K (ℕ →ᵇ K) (1 + a.toBCF) z) i‖ = ‖z i‖ := by
    intro i
    have hai : ‖a i‖ < 1 :=
      ((ZeroAtInftyContinuousMap.norm_toBCF_eq_norm (f := a)) ▸
        BoundedContinuousFunction.norm_coe_le_norm a.toBCF i).trans_lt (mem_ball_zero_iff.mp ha)
    have h1 : ‖(1 : K) + a i‖ = 1 := by
      rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hai.ne'),
        norm_one, max_eq_left hai.le]
    have he : (ContinuousLinearMap.mul K (ℕ →ᵇ K) (1 + a.toBCF) z) i = (1 + a i) * z i := by
      simp [add_mul]
    rw [he, norm_mul, h1, one_mul]
  refine le_antisymm ?_ ?_
  · exact (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr fun i =>
      (hpt i).trans_le (BoundedContinuousFunction.norm_coe_le_norm z i)
  · exact (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr fun i =>
      (hpt i).symm.trans_le (BoundedContinuousFunction.norm_coe_le_norm _ i)

/-- The transition `a ↦ D_{1+a}` is analytic everywhere (it is affine). -/
theorem analyticAt_mul_one_add (a₀ : C₀(ℕ, K)) :
    AnalyticAt K (fun a : C₀(ℕ, K) => ContinuousLinearMap.mul K (ℕ →ᵇ K) (1 + a.toBCF)) a₀ := by
  have h : (fun a : C₀(ℕ, K) => ContinuousLinearMap.mul K (ℕ →ᵇ K) (1 + a.toBCF)) =
      fun a => 1 + ((ContinuousLinearMap.mul K (ℕ →ᵇ K)).comp (toBCFCLM K)) a := by
    funext a
    exact mul_one_add a
  rw [h]
  exact analyticAt_const.add (ContinuousLinearMap.analyticAt _ _)

/-- The inverse transition `a ↦ D_{1+a}⁻¹` is analytic on the open unit ball of `c₀(ℕ, K)`. -/
theorem analyticOnNhd_inverse_mul_one_add [CompleteSpace K] :
    AnalyticOnNhd K
      (fun a : C₀(ℕ, K) => Ring.inverse (ContinuousLinearMap.mul K (ℕ →ᵇ K) (1 + a.toBCF)))
      (Metric.ball (0 : C₀(ℕ, K)) 1) := fun a ha =>
  AnalyticAt.comp (g := Ring.inverse)
    (f := fun a : C₀(ℕ, K) => ContinuousLinearMap.mul K (ℕ →ᵇ K) (1 + a.toBCF))
    (analyticOnNhd_inverse _ (isUnit_mul_one_add ha)) (analyticAt_mul_one_add a)

/-- `W ∘ (D_{1+a}, …, D_{1+a}) = A(id + D_a)(W)`. -/
theorem compContinuousLinearMap_mul_one_add {ι : Type v} [Fintype ι] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace K F] (W : (ℕ →ᵇ K) [⋀^ι]→L[K] F) (a : C₀(ℕ, K)) :
    W.compContinuousLinearMap (ContinuousLinearMap.mul K (ℕ →ᵇ K) (1 + a.toBCF)) =
      ContinuousAlternatingMap.compContinuousLinearMapCLM
        (ContinuousLinearMap.id K (ℕ →ᵇ K) + ContinuousLinearMap.mul K (ℕ →ᵇ K) a.toBCF) W := by
  rw [mul_one_add]
  rfl

/-- Non-analyticity of the induced section, from Proposition C.6 at `u₀ = id`. -/
theorem not_analyticAt_compContinuousLinearMap_mul_one_add {ι : Type v} [Fintype ι] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace K F] (W : (ℕ →ᵇ K) [⋀^ι]→L[K] F) (a₀ : C₀(ℕ, K))
    (hC6 : ¬ AnalyticAt K
      (fun a : C₀(ℕ, K) =>
        ContinuousAlternatingMap.compContinuousLinearMapCLM
          (ContinuousLinearMap.id K (ℕ →ᵇ K) + ContinuousLinearMap.mul K (ℕ →ᵇ K) a.toBCF) W)
      a₀) :
    ¬ AnalyticAt K
      (fun a : C₀(ℕ, K) =>
        W.compContinuousLinearMap (ContinuousLinearMap.mul K (ℕ →ᵇ K) (1 + a.toBCF))) a₀ := by
  simp_rw [compContinuousLinearMap_mul_one_add]
  exact hC6

/-- Corollary C.7, first part: over `K₁ = κ((X))`, on the open unit ball `U` of `c₀(ℕ, K₁)` the
transitions `D_{1+a}` are isometric units of `L(E₁, E₁)`, and the transition and its inverse are
analytic on `U`. -/
theorem laurent_part1 (κ : Type u) [Field κ] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] :
    (∀ a ∈ Metric.ball (0 : C₀(ℕ, LaurentField κ r)) 1, ∀ z : ℕ →ᵇ LaurentField κ r,
      ‖ContinuousLinearMap.mul (LaurentField κ r) (ℕ →ᵇ LaurentField κ r) (1 + a.toBCF) z‖ =
        ‖z‖) ∧
    (∀ a ∈ Metric.ball (0 : C₀(ℕ, LaurentField κ r)) 1,
      IsUnit (ContinuousLinearMap.mul (LaurentField κ r) (ℕ →ᵇ LaurentField κ r)
        (1 + a.toBCF))) ∧
    AnalyticOnNhd (LaurentField κ r)
      (fun a : C₀(ℕ, LaurentField κ r) =>
        ContinuousLinearMap.mul (LaurentField κ r) (ℕ →ᵇ LaurentField κ r) (1 + a.toBCF))
      (Metric.ball (0 : C₀(ℕ, LaurentField κ r)) 1) ∧
    AnalyticOnNhd (LaurentField κ r)
      (fun a : C₀(ℕ, LaurentField κ r) => Ring.inverse
        (ContinuousLinearMap.mul (LaurentField κ r) (ℕ →ᵇ LaurentField κ r) (1 + a.toBCF)))
      (Metric.ball (0 : C₀(ℕ, LaurentField κ r)) 1) :=
  ⟨fun _ ha => norm_mul_one_add_apply ha, fun _ ha => isUnit_mul_one_add ha,
    fun a _ => analyticAt_mul_one_add a, analyticOnNhd_inverse_mul_one_add⟩

/-- Corollary C.7, second part: over `K₁ = κ((X))`, if `a ↦ A(u₀ + D_a)(W_B)` is analytic at no
point for every `u₀` (Proposition C.6), then the chart-`τ₀` expression
`a ↦ W_B ∘ (D_{1+a}, …, D_{1+a})` is analytic at no point of the open unit ball. -/
theorem not_analyticAt_wedge_mul_one_add (κ : Type u) [Field κ] (r : ℝ≥0) [Fact (0 < r)]
    [Fact (r < 1)] (k : ℕ)
    (hC6 : ∀ (u₀ : (ℕ →ᵇ LaurentField κ r) →L[LaurentField κ r] (ℕ →ᵇ LaurentField κ r))
      (a₀ : C₀(ℕ, LaurentField κ r)),
      ¬ AnalyticAt (LaurentField κ r)
        (fun a : C₀(ℕ, LaurentField κ r) =>
          ContinuousAlternatingMap.compContinuousLinearMapCLM
            (u₀ + ContinuousLinearMap.mul (LaurentField κ r) (ℕ →ᵇ LaurentField κ r) a.toBCF)
            (completedExteriorWedge (LaurentField κ r) ℕ k)) a₀) :
    ∀ a₀ ∈ Metric.ball (0 : C₀(ℕ, LaurentField κ r)) 1,
      ¬ AnalyticAt (LaurentField κ r)
        (fun a : C₀(ℕ, LaurentField κ r) =>
          (completedExteriorWedge (LaurentField κ r) ℕ k).compContinuousLinearMap
            (ContinuousLinearMap.mul (LaurentField κ r) (ℕ →ᵇ LaurentField κ r)
              (1 + a.toBCF))) a₀ := fun a₀ _ =>
  not_analyticAt_compContinuousLinearMap_mul_one_add
    (completedExteriorWedge (LaurentField κ r) ℕ k) a₀ (hC6 _ a₀)

end AlternatingAnalytic.DiagonalTransitions
