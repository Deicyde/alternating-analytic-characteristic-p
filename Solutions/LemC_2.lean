import AlternatingAnalytic.Analysis.LaurentField
import AlternatingAnalytic.Analysis.ProjectiveExterior

/-!
# Proof of Lemma C.2

Uses `projectiveExteriorSeminorm_eq_iInf_wedgeCost` to identify `projNorm` with the library
seminorm, then `coordinateExteriorArray`, `completedExteriorArray` and `completedExteriorWedge`
and their lemmas in `Analysis/ProjectiveExterior.lean`.
-/

set_option backward.isDefEq.respectTransparency false

open scoped NNReal BoundedContinuousFunction

namespace AlternatingAnalyticChallenge.LemC_2

open AlternatingAnalytic

universe u

/-- The projective exterior norm `‖ω‖_π`: the infimum, over all finite decompositions
`ω = ∑_j x_{j,1} ∧ ⋯ ∧ x_{j,k}` (lists of `k`-tuples), of `∑_j ∏_i ‖x_{j,i}‖`. -/
noncomputable def projNorm (K : Type*) [NormedField K] (V : Type*) [SeminormedAddCommGroup V]
    [NormedSpace K V] (k : ℕ) (ω : ⋀[K]^k V) : ℝ :=
  ⨅ l : {l : List (Fin k → V) // (l.map (exteriorPower.ιMulti K k)).sum = ω},
    (l.1.map fun x => ∏ i, ‖x i‖).sum

/-- The canonical map from `Λ = ⋀[K₁]^k E₁` into the completion `B`. -/
noncomputable def toB (κ : Type u) [Field κ] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] (k : ℕ)
    (ω : ⋀[LaurentField κ r]^k (ℕ →ᵇ LaurentField κ r)) :
    ProjectiveExteriorCompletion (LaurentField κ r) ℕ k :=
  ((show ProjectiveExterior (LaurentField κ r) ℕ k from ω :
    ProjectiveExterior (LaurentField κ r) ℕ k) :
      ProjectiveExteriorCompletion (LaurentField κ r) ℕ k)

/-- `‖·‖_π` is a `K₁`-norm on `Λ`, and `‖x₁ ∧ ⋯ ∧ x_k‖_π ≤ ∏ i, ‖x i‖`. -/
theorem part1_projNorm_isNorm
    (κ : Type u) [Field κ] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] (k : ℕ) (hk : 1 ≤ k) :
    (∀ ω η : ⋀[LaurentField κ r]^k (ℕ →ᵇ LaurentField κ r),
      projNorm (LaurentField κ r) (ℕ →ᵇ LaurentField κ r) k (ω + η) ≤
        projNorm (LaurentField κ r) (ℕ →ᵇ LaurentField κ r) k ω +
          projNorm (LaurentField κ r) (ℕ →ᵇ LaurentField κ r) k η) ∧
    (∀ (a : LaurentField κ r) (ω : ⋀[LaurentField κ r]^k (ℕ →ᵇ LaurentField κ r)),
      projNorm (LaurentField κ r) (ℕ →ᵇ LaurentField κ r) k (a • ω) =
        ‖a‖ * projNorm (LaurentField κ r) (ℕ →ᵇ LaurentField κ r) k ω) ∧
    (∀ ω : ⋀[LaurentField κ r]^k (ℕ →ᵇ LaurentField κ r),
      projNorm (LaurentField κ r) (ℕ →ᵇ LaurentField κ r) k ω = 0 ↔ ω = 0) ∧
    (∀ x : Fin k → (ℕ →ᵇ LaurentField κ r),
      projNorm (LaurentField κ r) (ℕ →ᵇ LaurentField κ r) k
        (exteriorPower.ιMulti (LaurentField κ r) k x) ≤ ∏ i, ‖x i‖) := by
  have key : ∀ ω : ⋀[LaurentField κ r]^k (ℕ →ᵇ LaurentField κ r),
      projNorm (LaurentField κ r) (ℕ →ᵇ LaurentField κ r) k ω = projectiveExteriorSeminorm ω := by
    intro ω
    rw [projectiveExteriorSeminorm_eq_iInf_wedgeCost (⟨0, hk⟩ : Fin k) ω]
    unfold projNorm
    exact Equiv.iInf_congr (Equiv.subtypeEquiv FreeAddMonoid.ofList (fun l => by
      simp [exteriorWedgeSum, FreeAddMonoid.lift_apply])) (fun l => by simp [exteriorWedgeCost])
  refine ⟨fun ω η => ?_, fun a ω => ?_, fun ω => ?_, fun x => ?_⟩
  · rw [key, key, key]; exact map_add_le_add _ _ _
  · rw [key, key]; exact map_smul_eq_mul _ _ _
  · rw [key]; exact boundedFunction_projectiveExteriorSeminorm_eq_zero_iff ω
  · rw [key]; exact projectiveExteriorSeminorm_ιMulti_le x

/-- The determinant array `Ω^{K₁}` is `K₁`-linear and injective, with
`‖Ω^{K₁}(ω)‖_∞ ≤ ‖ω‖_π`. -/
theorem part2_determinantArray
    (κ : Type u) [Field κ] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] (k : ℕ) (hk : 1 ≤ k) :
    ∃ Ω : (⋀[LaurentField κ r]^k (ℕ →ᵇ LaurentField κ r)) →ₗ[LaurentField κ r]
        ((Fin k → ℕ) → LaurentField κ r),
      (∀ (x : Fin k → (ℕ →ᵇ LaurentField κ r)) (c : Fin k → ℕ),
        Ω (exteriorPower.ιMulti (LaurentField κ r) k x) c =
          Matrix.det (fun a b => x b (c a))) ∧
      Function.Injective Ω ∧
      (∀ (ω : ⋀[LaurentField κ r]^k (ℕ →ᵇ LaurentField κ r)) (c : Fin k → ℕ),
        ‖Ω ω c‖ ≤ projNorm (LaurentField κ r) (ℕ →ᵇ LaurentField κ r) k ω) := by
  have key : ∀ ω : ⋀[LaurentField κ r]^k (ℕ →ᵇ LaurentField κ r),
      projNorm (LaurentField κ r) (ℕ →ᵇ LaurentField κ r) k ω = projectiveExteriorSeminorm ω := by
    intro ω
    rw [projectiveExteriorSeminorm_eq_iInf_wedgeCost (⟨0, hk⟩ : Fin k) ω]
    unfold projNorm
    exact Equiv.iInf_congr (Equiv.subtypeEquiv FreeAddMonoid.ofList (fun l => by
      simp [exteriorWedgeSum, FreeAddMonoid.lift_apply])) (fun l => by simp [exteriorWedgeCost])
  refine ⟨coordinateExteriorArray boundedFunctionCoordinates, fun x c => ?_,
    coordinateExteriorArray_injective _ boundedFunctionCoordinates_injective, fun ω c => ?_⟩
  · simpa only [boundedFunctionCoordinates_apply] using coordinateExteriorArray_ιMulti
      (boundedFunctionCoordinates (K := LaurentField κ r) (S := ℕ)) x c
  · rw [key]; exact norm_coordinateExteriorArray_le _ (fun f s => f.norm_coe_le_norm s) ω c

/-- `B` is the completion of `(Λ, ‖·‖_π)`, the extension `J` of `Ω^{K₁}` has norm at most one,
and `W_B(x) = x₁ ∧ ⋯ ∧ x_k` is a continuous alternating map of norm at most one with
`J (W_B x) = Ω^{K₁}(x₁ ∧ ⋯ ∧ x_k)`. -/
theorem part3_completion
    (κ : Type u) [Field κ] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] (k : ℕ) (hk : 1 ≤ k) :
    CompleteSpace (ProjectiveExteriorCompletion (LaurentField κ r) ℕ k) ∧
    (∀ (a : LaurentField κ r) (ω η : ⋀[LaurentField κ r]^k (ℕ →ᵇ LaurentField κ r)),
      toB κ r k (a • ω + η) = a • toB κ r k ω + toB κ r k η) ∧
    (∀ ω : ⋀[LaurentField κ r]^k (ℕ →ᵇ LaurentField κ r),
      ‖toB κ r k ω‖ = projNorm (LaurentField κ r) (ℕ →ᵇ LaurentField κ r) k ω) ∧
    DenseRange (toB κ r k) ∧
    ∃ J : ProjectiveExteriorCompletion (LaurentField κ r) ℕ k →L[LaurentField κ r]
        ((Fin k → ℕ) →ᵇ LaurentField κ r),
      ‖J‖ ≤ 1 ∧
      (∀ (x : Fin k → (ℕ →ᵇ LaurentField κ r)) (c : Fin k → ℕ),
        J (toB κ r k (exteriorPower.ιMulti (LaurentField κ r) k x)) c =
          Matrix.det (fun a b => x b (c a))) ∧
      ∃ W : (ℕ →ᵇ LaurentField κ r) [⋀^Fin k]→L[LaurentField κ r]
          ProjectiveExteriorCompletion (LaurentField κ r) ℕ k,
        (∀ x : Fin k → (ℕ →ᵇ LaurentField κ r),
          W x = toB κ r k (exteriorPower.ιMulti (LaurentField κ r) k x)) ∧
        ‖W‖ ≤ 1 ∧
        (∀ (x : Fin k → (ℕ →ᵇ LaurentField κ r)) (c : Fin k → ℕ),
          J (W x) c = Matrix.det (fun a b => x b (c a))) := by
  have key : ∀ ω : ⋀[LaurentField κ r]^k (ℕ →ᵇ LaurentField κ r),
      projNorm (LaurentField κ r) (ℕ →ᵇ LaurentField κ r) k ω = projectiveExteriorSeminorm ω := by
    intro ω
    rw [projectiveExteriorSeminorm_eq_iInf_wedgeCost (⟨0, hk⟩ : Fin k) ω]
    unfold projNorm
    exact Equiv.iInf_congr (Equiv.subtypeEquiv FreeAddMonoid.ofList (fun l => by
      simp [exteriorWedgeSum, FreeAddMonoid.lift_apply])) (fun l => by simp [exteriorWedgeCost])
  refine ⟨inferInstance, fun a ω η => ?_, fun ω => ?_, ?_,
    completedExteriorArray _ ℕ k, completedExteriorArray_norm_le _ ℕ k,
    fun x c => completedExteriorArray_wedge _ ℕ k x c, completedExteriorWedge _ ℕ k, fun x => rfl,
    completedExteriorWedge_norm_le _ ℕ k, completedExteriorArray_wedge _ ℕ k⟩
  · let ω' : ProjectiveExterior (LaurentField κ r) ℕ k := ω
    let η' : ProjectiveExterior (LaurentField κ r) ℕ k := η
    change ((a • ω' + η' : ProjectiveExterior (LaurentField κ r) ℕ k) :
      ProjectiveExteriorCompletion (LaurentField κ r) ℕ k) = a • (ω' :
        ProjectiveExteriorCompletion (LaurentField κ r) ℕ k) + (η' :
        ProjectiveExteriorCompletion (LaurentField κ r) ℕ k)
    rw [UniformSpace.Completion.coe_add, UniformSpace.Completion.coe_smul]
  · simp only [toB]
    rw [UniformSpace.Completion.norm_coe, ProjectiveExterior.norm_eq, key]
  · exact UniformSpace.Completion.denseRange_coe (α := ProjectiveExterior (LaurentField κ r) ℕ k)

end AlternatingAnalyticChallenge.LemC_2
