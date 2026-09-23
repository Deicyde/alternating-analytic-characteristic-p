import AlternatingAnalytic.Algebra.ExteriorFlattening

/-!
# Cofactor formulas and support bounds for exterior contractions

The contraction of a pure wedge is the cofactor expansion in the selected row.
All contractions lie in every supporting subspace, so their span has dimension at
most the exterior support dimension. The last-slot version has exactly one covector
for each of the other slots.
-/

namespace AlternatingAnalytic

open Module

variable {L : Type*} [Field L]
  {V : Type*} [AddCommGroup V] [Module L V] {n : ℕ}

/-- The cofactor formula for contraction in any selected slot. -/
theorem exteriorContraction_ιMulti (α : Fin (n + 1))
    (φ : Fin (n + 1) → Dual L V) (x : Fin (n + 1) → V) :
    exteriorContraction α φ (exteriorPower.ιMulti L (n + 1) x) =
      ∑ i : Fin (n + 1),
        ((-1 : L) ^ (α.val + i.val) *
          Matrix.det (fun a b : Fin n ↦ φ (α.succAbove a) (x (i.succAbove b)))) • x i := by
  apply (Module.Free.chooseBasis L V).eval_injective
  ext ψ
  change ψ _ = ψ _
  rw [exteriorContraction_eval, exteriorPower.alternatingMapToDual_apply_ιMulti]
  change Matrix.det (Matrix.transpose
    (Matrix.of (fun i j ↦ Function.update φ α ψ i (x j)))) = _
  rw [Matrix.det_transpose, Matrix.det_succ_row _ α]
  have hminor (i : Fin (n + 1)) :
      (Matrix.of (fun a b ↦ Function.update φ α ψ a (x b))).submatrix
        α.succAbove i.succAbove =
      Matrix.of (fun a b : Fin n ↦ φ (α.succAbove a) (x (i.succAbove b))) := by
    ext a b
    simp [Fin.succAbove_ne]
  simp only [Matrix.of_apply, Function.update_self, map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hminor]
  exact mul_right_comm _ _ _

/-- Contract against a tuple of covectors in every slot except the last one. -/
noncomputable def exteriorLastContraction (φ : Fin n → Dual L V) :
    (⋀[L]^(n + 1) V) →ₗ[L] V :=
  exteriorContraction (Fin.last n) (Fin.lastCases 0 φ)

/-- The last-slot contraction is the signed sum of the corresponding cofactors. -/
theorem exteriorLastContraction_ιMulti (φ : Fin n → Dual L V) (x : Fin (n + 1) → V) :
    exteriorLastContraction φ (exteriorPower.ιMulti L (n + 1) x) =
      ∑ i : Fin (n + 1),
        ((-1 : L) ^ (n + i.val) *
          Matrix.det (fun a b : Fin n ↦ φ a (x (i.succAbove b)))) • x i := by
  simpa [exteriorLastContraction] using
    exteriorContraction_ιMulti (Fin.last n) (Fin.lastCases 0 φ) x

/-- Last-slot contractions preserve every supporting subspace. -/
theorem exteriorLastContraction_mem_support (φ : Fin n → Dual L V)
    (W : Submodule L V) {ω : ⋀[L]^(n + 1) V}
    (hω : ω ∈ exteriorPowerSubmodule (n + 1) W) :
    exteriorLastContraction φ ω ∈ W :=
  exteriorContraction_mem_support _ _ W hω

/-- The span of all last-slot contraction vectors of an exterior vector. -/
noncomputable def exteriorContractionSpan (ω : ⋀[L]^(n + 1) V) : Submodule L V :=
  Submodule.span L (Set.range (fun φ : Fin n → Dual L V ↦ exteriorLastContraction φ ω))

/-- The contraction span is contained in every supporting subspace. -/
theorem exteriorContractionSpan_le (W : Submodule L V) {ω : ⋀[L]^(n + 1) V}
    (hω : ω ∈ exteriorPowerSubmodule (n + 1) W) : exteriorContractionSpan ω ≤ W := by
  apply Submodule.span_le.mpr
  rintro _ ⟨φ, rfl⟩
  exact exteriorLastContraction_mem_support φ W hω

/-- The contraction span of an exterior vector is finite-dimensional. -/
theorem exteriorContractionSpan_finite (ω : ⋀[L]^(n + 1) V) :
    Module.Finite L (exteriorContractionSpan ω) := by
  obtain ⟨W, hW, hω⟩ := exists_finite_exterior_support ω
  let := hW
  exact Submodule.finiteDimensional_of_le (exteriorContractionSpan_le W hω)

/-- The dimension of the contraction span is a lower bound for exterior support dimension. -/
theorem exteriorContractionSpan_finrank_le (ω : ⋀[L]^(n + 1) V) :
    finrank L (exteriorContractionSpan ω) ≤ exteriorSupportDim ω := by
  obtain ⟨W, hW, hω, hdim⟩ := exteriorSupportDim_attained ω
  let := hW
  rw [← hdim]
  exact Submodule.finrank_mono (exteriorContractionSpan_le W hω)

/-- The cofactor formula, preservation of supports, and the contraction-span bound. -/
theorem exteriorLastContraction_properties :
    (∀ (φ : Fin n → Dual L V) (x : Fin (n + 1) → V),
      exteriorLastContraction φ (exteriorPower.ιMulti L (n + 1) x) =
        ∑ i : Fin (n + 1),
          ((-1 : L) ^ (n + i.val) *
            Matrix.det (fun a b : Fin n ↦ φ a (x (i.succAbove b)))) • x i) ∧
    (∀ (φ : Fin n → Dual L V) (W : Submodule L V) (ω : ⋀[L]^(n + 1) V),
      ω ∈ exteriorPowerSubmodule (n + 1) W → exteriorLastContraction φ ω ∈ W) ∧
    (∀ ω : ⋀[L]^(n + 1) V,
      finrank L (exteriorContractionSpan ω) ≤ exteriorSupportDim ω) := by
  exact ⟨exteriorLastContraction_ιMulti,
    fun φ W _ hω ↦ exteriorLastContraction_mem_support φ W hω,
    exteriorContractionSpan_finrank_le⟩

end AlternatingAnalytic
