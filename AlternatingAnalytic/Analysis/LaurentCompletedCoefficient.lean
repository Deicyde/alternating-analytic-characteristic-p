import AlternatingAnalytic.Analysis.LaurentAlgebraicCoefficient
import AlternatingAnalytic.Analysis.DenseCoefficientExtension
import AlternatingAnalytic.Analysis.ExteriorCoefficientGrowth
import AlternatingAnalytic.Analysis.UnitSumGrowth

/-! The actual completed coefficient map and the target's linearly growing block wedges. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped NNReal BoundedContinuousFunction

namespace AlternatingAnalytic

variable (κ : Type*) [Field κ] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)]
variable (S : Type*) [TopologicalSpace S] [DiscreteTopology S] (k : ℕ)

/-- The genuine constant coefficient of the completed determinant array. -/
def completedLaurentCoefficientArray :
    ProjectiveExteriorCompletion (LaurentField κ r) S k →ₗ[κ] ((Fin k → S) → κ) where
  toFun b := boundedLaurentCoeff κ r 0 (completedExteriorArray (LaurentField κ r) S k b)
  map_add' b c := by rw [map_add, boundedLaurentCoeff_add]
  map_smul' a b := by
    change boundedLaurentCoeff κ r 0
      (completedExteriorArray (LaurentField κ r) S k (a • b)) = _
    rw [← IsScalarTower.algebraMap_smul (LaurentField κ r) a b, map_smul,
      boundedLaurentCoeff_smul_const]
    rfl

/-- Passing to the Banach completion preserves the exterior coefficient and its sharp support bound. -/
theorem exists_completedLaurentCoefficient (α : Fin k) :
    ∃ η : ProjectiveExteriorCompletion (LaurentField κ r) S k →ₗ[κ] (⋀[κ]^k (S → κ)),
      (∀ b, determinantArray (η b) = completedLaurentCoefficientArray κ r S k b) ∧
      (∀ ω : ProjectiveExterior (LaurentField κ r) S k,
        η (ω : ProjectiveExteriorCompletion (LaurentField κ r) S k) =
          algebraicLaurentCoefficient κ r S k α ω) ∧
      (∀ b, (exteriorSupportDim (η b) : ℝ) ≤
        (k : ℝ) * geometricWeightMaximum r * ‖b‖) := by
  let i : ProjectiveExterior (LaurentField κ r) S k →ₗ[κ]
      ProjectiveExteriorCompletion (LaurentField κ r) S k :=
    (UniformSpace.Completion.toComplL : ProjectiveExterior (LaurentField κ r) S k →L[LaurentField κ r]
      ProjectiveExteriorCompletion (LaurentField κ r) S k).toLinearMap.restrictScalars κ
  have hi : Isometry i := (UniformSpace.Completion.toComplₗᵢ :
    ProjectiveExterior (LaurentField κ r) S k →ₗᵢ[LaurentField κ r]
      ProjectiveExteriorCompletion (LaurentField κ r) S k).isometry
  apply exists_denseCoefficientExtension i hi
    UniformSpace.Completion.denseRange_coe determinantArray determinantArray_injective
    (completedLaurentCoefficientArray κ r S k)
    ?_ (algebraicLaurentCoefficient κ r S k α) ?_
    (fun β => (exteriorSupportDim β : ℝ)) ((k : ℝ) * geometricWeightMaximum r)
    (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans (one_le_geometricWeightMaximum r)))
    (algebraicLaurentCoefficient_support_le κ r S k α)
  · intro b b' h
    apply boundedLaurentCoeff_eq_of_norm_sub_lt_one κ r
    rw [← map_sub]
    exact (norm_completedExteriorArray_le (LaurentField κ r) S k (b - b')).trans_lt h
  · intro ω
    change determinantArray (algebraicLaurentCoefficient κ r S k α ω) =
      boundedLaurentCoeff κ r 0
        ((projectiveExteriorArray (LaurentField κ r) S k).fromCompletion
          (ω : ProjectiveExteriorCompletion (LaurentField κ r) S k))
    rw [ContinuousLinearMap.fromCompletion_apply_coe]
    exact algebraicLaurentCoefficient_array κ r S k α ω

/-- The paper's coefficient-field linear map on the completed projective exterior target. -/
def completedLaurentCoefficient (α : Fin k) :
    ProjectiveExteriorCompletion (LaurentField κ r) S k →ₗ[κ] (⋀[κ]^k (S → κ)) :=
  (exists_completedLaurentCoefficient κ r S k α).choose

theorem completedLaurentCoefficient_array (α : Fin k)
    (b : ProjectiveExteriorCompletion (LaurentField κ r) S k) :
    determinantArray (completedLaurentCoefficient κ r S k α b) =
      boundedLaurentCoeff κ r 0 (completedExteriorArray (LaurentField κ r) S k b) :=
  (exists_completedLaurentCoefficient κ r S k α).choose_spec.1 b

theorem completedLaurentCoefficient_coe (α : Fin k)
    (ω : ProjectiveExterior (LaurentField κ r) S k) :
    completedLaurentCoefficient κ r S k α
      (ω : ProjectiveExteriorCompletion (LaurentField κ r) S k) =
      algebraicLaurentCoefficient κ r S k α ω :=
  (exists_completedLaurentCoefficient κ r S k α).choose_spec.2.1 ω

theorem completedLaurentCoefficient_support_le (α : Fin k)
    (b : ProjectiveExteriorCompletion (LaurentField κ r) S k) :
    (exteriorSupportDim (completedLaurentCoefficient κ r S k α b) : ℝ) ≤
      (k : ℝ) * geometricWeightMaximum r * ‖b‖ :=
  (exists_completedLaurentCoefficient κ r S k α).choose_spec.2.2 b

theorem completedLaurentCoefficient_unique (α : Fin k)
    (b : ProjectiveExteriorCompletion (LaurentField κ r) S k) (β : ⋀[κ]^k (S → κ))
    (hβ : determinantArray β =
      boundedLaurentCoeff κ r 0 (completedExteriorArray (LaurentField κ r) S k b)) :
    β = completedLaurentCoefficient κ r S k α b :=
  determinantArray_injective (hβ.trans (completedLaurentCoefficient_array κ r S k α b).symm)

/-- Coefficient-field pure wedges retain exactly their original exterior vector. -/
theorem completedLaurentCoefficient_constant_wedge (α : Fin k) (x : Fin k → (S → κ)) :
    completedLaurentCoefficient κ r S k α
      (completedExteriorWedge (LaurentField κ r) S k (fun i => constantLaurentArray κ r (x i))) =
      exteriorPower.ιMulti κ k x := by
  change completedLaurentCoefficient κ r S k α
    ((projectiveExteriorWedge (LaurentField κ r) S k (fun i => constantLaurentArray κ r (x i)) :
      ProjectiveExterior (LaurentField κ r) S k) :
      ProjectiveExteriorCompletion (LaurentField κ r) S k) = _
  rw [completedLaurentCoefficient_coe, algebraicLaurentCoefficient_constant_wedge]

/-- The actual completed Laurent exterior target has linearly growing unit block sums. -/
theorem laurentExterior_hasLinearUnitSumGrowth (hk : 2 ≤ k) :
    HasLinearUnitSumGrowth (ProjectiveExteriorCompletion (LaurentField κ r) ℕ k) := by
  let α : Fin k := ⟨0, by omega⟩
  refine ⟨laurentBlockWedge κ r k, geometricWeightMaximum r,
    zero_lt_one.trans_le (one_le_geometricWeightMaximum r), norm_laurentBlockWedge_le_one κ r k, ?_⟩
  apply exteriorCoefficient_block_growth hk (completedLaurentCoefficient κ r ℕ k α)
    (laurentBlockWedge κ r k)
    (fun j => completedLaurentCoefficient_constant_wedge κ r ℕ k α
      (fun i => Pi.single (k * j + i.val + 1) (1 : κ)))
    (zero_lt_one.trans_le (one_le_geometricWeightMaximum r))
    (completedLaurentCoefficient_support_le κ r ℕ k α)

theorem laurentExterior_not_hasEquivalentUltrametricNorm (hk : 2 ≤ k) :
    ¬ HasEquivalentUltrametricNorm (LaurentField κ r)
      (ProjectiveExteriorCompletion (LaurentField κ r) ℕ k) :=
  (laurentExterior_hasLinearUnitSumGrowth κ r k hk).not_hasEquivalentUltrametricNorm (LaurentField κ r)

end AlternatingAnalytic
