import AlternatingAnalytic.Analysis.LaurentWedgeCoefficient

/-!
# The coefficient map on the algebraic exterior power

For `ω` in the uncompleted projective exterior power `Λ^k` of `ℓ^∞(S, κ((X)))`, there is a
unique `η(ω) ∈ Λ^k_κ (S → κ)` whose determinant array is the constant coefficient of the
determinant array of `ω`, and `sdim η(ω) ≤ k M_r ‖ω‖`. This is Proposition C.3 before
completion (`M_r` is `geometricWeightMaximum r`). The argument `α : Fin k` only records
that `k ≥ 1`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Module
open scoped NNReal BoundedContinuousFunction

namespace AlternatingAnalytic

variable (κ : Type*) [Field κ] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)]
variable (S : Type*) [TopologicalSpace S] (k : ℕ)

/-- `κ` acts on the projective exterior power through constant Laurent series. -/
instance laurentProjectiveExteriorModule : Module κ (ProjectiveExterior (LaurentField κ r) S k) :=
  Module.compHom _ (algebraMap κ (LaurentField κ r))

instance laurentProjectiveExteriorScalarTower :
    IsScalarTower κ (LaurentField κ r) (ProjectiveExterior (LaurentField κ r) S k) :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- `κ` acts on the completed projective exterior power through constant Laurent series. -/
instance laurentCompletedExteriorModule :
    Module κ (ProjectiveExteriorCompletion (LaurentField κ r) S k) :=
  Module.compHom _ (algebraMap κ (LaurentField κ r))

instance laurentCompletedExteriorScalarTower :
    IsScalarTower κ (LaurentField κ r) (ProjectiveExteriorCompletion (LaurentField κ r) S k) :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

variable [DiscreteTopology S]

/-- The constant coefficient `coeff₀` of the determinant array, as a `κ`-linear map. -/
def algebraicLaurentCoefficientArray :
    ProjectiveExterior (LaurentField κ r) S k →ₗ[κ] ((Fin k → S) → κ) where
  toFun ω := boundedLaurentCoeff κ r 0 (projectiveExteriorArray (LaurentField κ r) S k ω)
  map_add' ω η := by rw [map_add, boundedLaurentCoeff_add]
  map_smul' a ω := by
    change boundedLaurentCoeff κ r 0
      (projectiveExteriorArray (LaurentField κ r) S k (a • ω)) = _
    rw [← IsScalarTower.algebraMap_smul (LaurentField κ r) a ω, map_smul,
      boundedLaurentCoeff_smul_const]
    rfl

/-- On a pure wedge, the coefficient array is `coeff₀` of the determinant form. -/
theorem algebraicLaurentCoefficientArray_wedge (x : Fin k → (S →ᵇ LaurentField κ r)) :
    algebraicLaurentCoefficientArray κ r S k (exteriorPower.ιMulti (LaurentField κ r) k x) =
      boundedLaurentCoeff κ r 0 (laurentDeterminantForm κ r k x) := rfl

omit [DiscreteTopology S] in
/-- In positive degree, every `ω` is a finite sum of pure wedges with no scalar weights. -/
theorem exists_unweighted_exterior_decomposition (α : Fin k)
    (ω : ProjectiveExterior (LaurentField κ r) S k) :
    ∃ q : FreeAddMonoid (Fin k → (S →ᵇ LaurentField κ r)), exteriorWedgeSum q = ω := by
  obtain ⟨p, hp⟩ := exists_exterior_decomposition (show ⋀[LaurentField κ r]^k _ from ω)
  exact ⟨_, (exteriorWedgeSum_absorb α p).trans hp⟩

/-- The coefficient array of a finite sum of pure wedges is a determinant array over `κ`. -/
theorem exists_coefficient_of_wedgeSum
    (q : FreeAddMonoid (Fin k → (S →ᵇ LaurentField κ r))) :
    ∃ β : ⋀[κ]^k (S → κ), determinantArray β =
      algebraicLaurentCoefficientArray κ r S k (exteriorWedgeSum q) := by
  induction q using FreeAddMonoid.inductionOn with
  | zero => exact ⟨0, by simp only [map_zero]⟩
  | of x =>
    obtain ⟨β, hβ, _⟩ := exists_laurentWedgeCoefficient κ r k x
    exact ⟨β, hβ⟩
  | add p q hp hq =>
    obtain ⟨β, hβ⟩ := hp
    obtain ⟨γ, hγ⟩ := hq
    exact ⟨β + γ, by rw [map_add, hβ, hγ, map_add, map_add]⟩

/-- Every coefficient array is the determinant array of some `β ∈ Λ^k_κ (S → κ)`. -/
theorem exists_algebraicLaurentCoefficient (α : Fin k)
    (ω : ProjectiveExterior (LaurentField κ r) S k) :
    ∃ β : ⋀[κ]^k (S → κ), determinantArray β = algebraicLaurentCoefficientArray κ r S k ω := by
  obtain ⟨q, rfl⟩ := exists_unweighted_exterior_decomposition κ r S k α ω
  exact exists_coefficient_of_wedgeSum κ r S k q

/-- The coefficient map `η`: the unique exterior vector over `κ` whose determinant array
is `coeff₀` of the determinant array of `ω`. -/
def algebraicLaurentCoefficient (α : Fin k) :
    ProjectiveExterior (LaurentField κ r) S k →ₗ[κ] (⋀[κ]^k (S → κ)) where
  toFun ω := Classical.choose (exists_algebraicLaurentCoefficient κ r S k α ω)
  map_add' ω η := by
    apply determinantArray_injective
    calc
      _ = algebraicLaurentCoefficientArray κ r S k (ω + η) :=
        Classical.choose_spec (exists_algebraicLaurentCoefficient κ r S k α (ω + η))
      _ = algebraicLaurentCoefficientArray κ r S k ω +
          algebraicLaurentCoefficientArray κ r S k η := map_add _ ω η
      _ = determinantArray (Classical.choose (exists_algebraicLaurentCoefficient κ r S k α ω)) +
          determinantArray (Classical.choose (exists_algebraicLaurentCoefficient κ r S k α η)) :=
        congrArg₂ (· + ·)
          (Classical.choose_spec (exists_algebraicLaurentCoefficient κ r S k α ω)).symm
          (Classical.choose_spec (exists_algebraicLaurentCoefficient κ r S k α η)).symm
      _ = _ := (map_add determinantArray _ _).symm
  map_smul' a ω := by
    apply determinantArray_injective
    calc
      _ = algebraicLaurentCoefficientArray κ r S k (a • ω) :=
        Classical.choose_spec (exists_algebraicLaurentCoefficient κ r S k α (a • ω))
      _ = a • algebraicLaurentCoefficientArray κ r S k ω := map_smul _ a ω
      _ = a • determinantArray
          (Classical.choose (exists_algebraicLaurentCoefficient κ r S k α ω)) :=
        congrArg (a • ·)
          (Classical.choose_spec (exists_algebraicLaurentCoefficient κ r S k α ω)).symm
      _ = _ := (map_smul determinantArray a _).symm

/-- The determinant array of `η ω` is the coefficient array of `ω`. -/
theorem algebraicLaurentCoefficient_array (α : Fin k)
    (ω : ProjectiveExterior (LaurentField κ r) S k) :
    determinantArray (algebraicLaurentCoefficient κ r S k α ω) =
      boundedLaurentCoeff κ r 0 (projectiveExteriorArray (LaurentField κ r) S k ω) :=
  Classical.choose_spec (exists_algebraicLaurentCoefficient κ r S k α ω)

/-- `η ω` is the only exterior vector with this determinant array. -/
theorem algebraicLaurentCoefficient_unique (α : Fin k)
    (ω : ProjectiveExterior (LaurentField κ r) S k) (β : ⋀[κ]^k (S → κ))
    (hβ : determinantArray β =
      boundedLaurentCoeff κ r 0 (projectiveExteriorArray (LaurentField κ r) S k ω)) :
    β = algebraicLaurentCoefficient κ r S k α ω :=
  determinantArray_injective (hβ.trans (algebraicLaurentCoefficient_array κ r S k α ω).symm)

/-- `η` sends a wedge of constant arrays to the same wedge over `κ`. -/
theorem algebraicLaurentCoefficient_constant_wedge (α : Fin k) (x : Fin k → (S → κ)) :
    algebraicLaurentCoefficient κ r S k α
      (projectiveExteriorWedge (LaurentField κ r) S k (fun i ↦ constantLaurentArray κ r (x i))) =
      exteriorPower.ιMulti κ k x := by
  apply determinantArray_injective
  rw [algebraicLaurentCoefficient_array]
  change boundedLaurentCoeff κ r 0
    (laurentDeterminantForm κ r k (fun i ↦ constantLaurentArray κ r (x i))) = _
  rw [laurentDeterminantForm_constant, boundedLaurentCoeff_constantLaurentArray]

/-- The support estimate for a pure wedge. -/
theorem algebraicLaurentCoefficient_wedge_support_le (α : Fin k)
    (x : Fin k → (S →ᵇ LaurentField κ r)) :
    (exteriorSupportDim (algebraicLaurentCoefficient κ r S k α
      (exteriorPower.ιMulti (LaurentField κ r) k x)) : ℝ) ≤
      (k : ℝ) * geometricWeightMaximum r * ∏ i, ‖x i‖ := by
  obtain ⟨β, hβ, hbound⟩ := exists_laurentWedgeCoefficient κ r k x
  have heq : β = algebraicLaurentCoefficient κ r S k α
      (exteriorPower.ιMulti (LaurentField κ r) k x) :=
    algebraicLaurentCoefficient_unique κ r S k α _ β hβ
  rwa [← heq]

/-- The support estimate for a finite sum of pure wedges, with its decomposition cost. -/
theorem algebraicLaurentCoefficient_wedgeSum_support_le (α : Fin k)
    (q : FreeAddMonoid (Fin k → (S →ᵇ LaurentField κ r))) :
    (exteriorSupportDim (algebraicLaurentCoefficient κ r S k α (exteriorWedgeSum q)) : ℝ) ≤
      (k : ℝ) * geometricWeightMaximum r * exteriorWedgeCost q := by
  induction q using FreeAddMonoid.inductionOn with
  | zero => simp only [map_zero, exteriorSupportDim_zero, Nat.cast_zero,
      exteriorWedgeCost, FreeAddMonoid.toList_zero, List.map_nil, List.sum_nil, mul_zero, le_refl]
  | of x =>
    simpa only [exteriorWedgeSum, FreeAddMonoid.lift_eval_of, exteriorWedgeCost,
      FreeAddMonoid.toList_of, List.map_singleton,
      List.sum_singleton] using algebraicLaurentCoefficient_wedge_support_le κ r S k α x
  | add p q hp hq =>
    rw [map_add, map_add]
    calc
      _ ≤ (exteriorSupportDim (algebraicLaurentCoefficient κ r S k α (exteriorWedgeSum p)) : ℝ) +
          exteriorSupportDim (algebraicLaurentCoefficient κ r S k α (exteriorWedgeSum q)) :=
        by exact_mod_cast (exteriorSupportDim_add_le
          (algebraicLaurentCoefficient κ r S k α (exteriorWedgeSum p))
          (algebraicLaurentCoefficient κ r S k α (exteriorWedgeSum q)))
      _ ≤ _ := add_le_add hp hq
      _ = _ := by simp only [exteriorWedgeCost, FreeAddMonoid.toList_add,
        List.map_append, List.sum_append, mul_add]

/-- The support estimate `sdim (η ω) ≤ k M_r ‖ω‖` on the algebraic exterior power. -/
theorem algebraicLaurentCoefficient_support_le (α : Fin k)
    (ω : ProjectiveExterior (LaurentField κ r) S k) :
    (exteriorSupportDim (algebraicLaurentCoefficient κ r S k α ω) : ℝ) ≤
      (k : ℝ) * geometricWeightMaximum r * ‖ω‖ := by
  have hk : 0 < (k : ℝ) := by exact_mod_cast (Nat.zero_le α.val).trans_lt α.isLt
  have hC : 0 < (k : ℝ) * geometricWeightMaximum r :=
    mul_pos hk (zero_lt_one.trans_le (one_le_geometricWeightMaximum r))
  have hex : Nonempty {q : FreeAddMonoid (Fin k → (S →ᵇ LaurentField κ r)) //
      exteriorWedgeSum q = ω} :=
    nonempty_subtype.mpr (exists_unweighted_exterior_decomposition κ r S k α ω)
  have h : (exteriorSupportDim (algebraicLaurentCoefficient κ r S k α ω) : ℝ) /
      ((k : ℝ) * geometricWeightMaximum r) ≤ ‖ω‖ := by
    rw [ProjectiveExterior.norm_eq, projectiveExteriorSeminorm_eq_iInf_wedgeCost α]
    apply le_ciInf
    intro q
    apply (div_le_iff₀ hC).2
    simpa only [q.property, mul_comm] using
      algebraicLaurentCoefficient_wedgeSum_support_le κ r S k α q.val
  simpa only [mul_comm] using (div_le_iff₀ hC).1 h

/-- The properties of `η` on the algebraic exterior power: determinant array, uniqueness,
constant wedges, support estimate. -/
theorem algebraicLaurentCoefficient_properties (α : Fin k) :
    (∀ ω : ProjectiveExterior (LaurentField κ r) S k,
      determinantArray (algebraicLaurentCoefficient κ r S k α ω) =
        boundedLaurentCoeff κ r 0 (projectiveExteriorArray (LaurentField κ r) S k ω)) ∧
    (∀ (ω : ProjectiveExterior (LaurentField κ r) S k) (β : ⋀[κ]^k (S → κ)),
      determinantArray β = boundedLaurentCoeff κ r 0
        (projectiveExteriorArray (LaurentField κ r) S k ω) →
      β = algebraicLaurentCoefficient κ r S k α ω) ∧
    (∀ x : Fin k → (S → κ), algebraicLaurentCoefficient κ r S k α
      (projectiveExteriorWedge (LaurentField κ r) S k (fun i ↦ constantLaurentArray κ r (x i))) =
      exteriorPower.ιMulti κ k x) ∧
    (∀ ω : ProjectiveExterior (LaurentField κ r) S k,
      (exteriorSupportDim (algebraicLaurentCoefficient κ r S k α ω) : ℝ) ≤
        (k : ℝ) * geometricWeightMaximum r * ‖ω‖) :=
  ⟨algebraicLaurentCoefficient_array κ r S k α,
    algebraicLaurentCoefficient_unique κ r S k α,
    algebraicLaurentCoefficient_constant_wedge κ r S k α,
    algebraicLaurentCoefficient_support_le κ r S k α⟩

end AlternatingAnalytic
