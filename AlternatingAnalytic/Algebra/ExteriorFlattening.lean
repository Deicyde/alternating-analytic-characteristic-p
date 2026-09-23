import AlternatingAnalytic.Algebra.DeterminantArray
import AlternatingAnalytic.Algebra.TensorSupport
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Flattening ranks of determinant arrays

Contracting the antisymmetrized tensor leaves a vector in every supporting subspace.
Evaluating that vector gives a column of the determinant-array flattening. Therefore
the column space has dimension at most the support dimension of the exterior vector.
-/

open scoped TensorProduct

namespace AlternatingAnalytic

open Module

variable {L : Type*} [Field L]
  {V : Type*} [AddCommGroup V] [Module L V] {k : ℕ}

/-- Pairing the remaining tensor factor is the full tensor pairing, with the chosen
covector inserted in that factor. -/
theorem tensorContraction_eval (α : Fin k) (φ : Fin k → Dual L V) (ψ : Dual L V)
    (τ : ⨂[L]^k V) :
    ψ (tensorContraction L α φ τ) =
      TensorPower.multilinearMapToDual L V k (Function.update φ α ψ) τ := by
  have hmaps : ψ.comp (tensorContraction L α φ) =
      TensorPower.multilinearMapToDual L V k (Function.update φ α ψ) := by
    apply PiTensorProduct.ext
    ext x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      tensorContraction_tprod, map_smul, smul_eq_mul,
      TensorPower.multilinearMapToDual_apply_tprod]
    simp_rw [Function.apply_update (fun j ↦ fun f : Dual L V ↦ f (x j))]
    rw [Finset.prod_update_of_mem (Finset.mem_univ α)]
    simp only [Finset.sdiff_singleton_eq_erase]
    exact mul_comm _ _
  exact LinearMap.congr_fun hmaps τ

/-- Contract an exterior vector against covectors in all slots except `α`. -/
noncomputable def exteriorContraction (α : Fin k) (φ : Fin k → Dual L V) :
    (⋀[L]^k V) →ₗ[L] V :=
  (tensorContraction L α φ).comp (exteriorPower.toTensorPower L V k)

/-- Evaluation of an exterior contraction is the determinant pairing. -/
theorem exteriorContraction_eval (α : Fin k) (φ : Fin k → Dual L V) (ψ : Dual L V)
    (ω : ⋀[L]^k V) :
    ψ (exteriorContraction α φ ω) =
      exteriorPower.alternatingMapToDual L V k (Function.update φ α ψ) ω :=
  tensorContraction_eval α φ ψ (exteriorPower.toTensorPower L V k ω)

/-- Every exterior contraction lies in every subspace supporting its input. -/
theorem exteriorContraction_mem_support (α : Fin k) (φ : Fin k → Dual L V)
    (W : Submodule L V) {ω : ⋀[L]^k V} (hω : ω ∈ exteriorPowerSubmodule k W) :
    exteriorContraction α φ ω ∈ W := by
  classical
  obtain ⟨η, rfl⟩ := hω
  have hη : η ∈ Submodule.span L (Set.range (exteriorPower.ιMulti L k)) := by
    rw [exteriorPower.ιMulti_span]
    exact Submodule.mem_top
  induction hη using Submodule.span_induction with
  | mem _ hx =>
    obtain ⟨x, rfl⟩ := hx
    simp only [exteriorPower.map_apply_ιMulti, exteriorContraction, LinearMap.comp_apply,
      exteriorPower.toTensorPower_apply_ιMulti, map_sum, Units.smul_def, map_zsmul,
      tensorContraction_tprod]
    apply Submodule.sum_mem
    intro σ hσ
    exact W.smul_of_tower_mem _ (W.smul_mem _ (x (σ α)).property)
  | zero => simp only [map_zero, Submodule.zero_mem]
  | add η θ _ _ hη hθ =>
    simpa only [map_add] using W.add_mem hη hθ
  | smul c η _ hη =>
    simpa only [map_smul] using W.smul_mem c hη

variable {S : Type*}

/-- Insert a value into one slot of a tuple on the remaining slots. -/
def tupleWithSlot (α : Fin k) (s : S) (c : {i : Fin k // i ≠ α} → S) : Fin k → S :=
  fun i ↦ if h : i = α then s else c ⟨i, h⟩

/-- The covectors associated to a tuple on the slots other than `α`.
The unused covector in slot `α` is zero. -/
def coordinateContractionForms (W : Submodule L (S → L)) (α : Fin k)
    (c : {i : Fin k // i ≠ α} → S) : Fin k → Dual L W :=
  fun i ↦ if h : i = α then 0 else (LinearMap.proj (c ⟨i, h⟩)).comp W.subtype

/-- A column function of the determinant array is an evaluation of a contraction vector. -/
theorem exteriorContraction_coordinate (W : Submodule L (S → L)) (α : Fin k)
    (c : {i : Fin k // i ≠ α} → S) (ω : ⋀[L]^k W) (s : S) :
    (exteriorContraction α (coordinateContractionForms W α c) ω : S → L) s =
      determinantArraySubmodule W ω (tupleWithSlot α s c) := by
  have hforms : Function.update (coordinateContractionForms W α c) α
      ((LinearMap.proj s).comp W.subtype) =
      (fun i ↦ (LinearMap.proj (tupleWithSlot α s c i)).comp W.subtype) := by
    funext i
    by_cases hi : i = α
    · subst i
      simp [tupleWithSlot]
    · simp [coordinateContractionForms, tupleWithSlot, hi]
  have h := exteriorContraction_eval α (coordinateContractionForms W α c)
    ((LinearMap.proj s).comp W.subtype) ω
  rw [hforms] at h
  change _ = exteriorEvaluationArray (fun s ↦ (LinearMap.proj s).comp W.subtype) ω
    (tupleWithSlot α s c) at h
  rw [← exteriorEvaluationArray_map] at h
  exact h

/-- A finite matrix obtained by varying one coordinate of a determinant array. -/
noncomputable def exteriorFlattening {R C : Type*} (W : Submodule L (S → L))
    (ω : ⋀[L]^k W) (α : Fin k) (rows : R → S)
    (columns : C → {i : Fin k // i ≠ α} → S) : Matrix R C L :=
  fun r c ↦ determinantArraySubmodule W ω (tupleWithSlot α (rows r) (columns c))

/-- Every column of a flattening belongs to the restriction image of any supporting subspace. -/
theorem exteriorFlattening_column_mem {R C : Type*} (W : Submodule L (S → L))
    (ω : ⋀[L]^k W) (α : Fin k) (rows : R → S)
    (columns : C → {i : Fin k // i ≠ α} → S)
    (U : Submodule L W) (hω : ω ∈ exteriorPowerSubmodule k U) (c : C) :
    (exteriorFlattening W ω α rows columns).col c ∈
      U.map (LinearMap.pi fun r ↦ (LinearMap.proj (rows r)).comp W.subtype) := by
  refine Submodule.mem_map.mpr
    ⟨exteriorContraction α (coordinateContractionForms W α (columns c)) ω,
      exteriorContraction_mem_support α _ U hω, ?_⟩
  funext r
  exact exteriorContraction_coordinate W α (columns c) ω (rows r)

/-- The rank of any finite determinant-array flattening is bounded by exterior support dimension. -/
theorem exteriorFlattening_rank_le {R C : Type*} [Fintype R] [Fintype C]
    (W : Submodule L (S → L)) (ω : ⋀[L]^k W) (α : Fin k) (rows : R → S)
    (columns : C → {i : Fin k // i ≠ α} → S) :
    (exteriorFlattening W ω α rows columns).rank ≤ exteriorSupportDim ω := by
  obtain ⟨U, hU, hω, hdim⟩ := exteriorSupportDim_attained ω
  let := hU
  let restriction : W →ₗ[L] (R → L) :=
    LinearMap.pi fun r ↦ (LinearMap.proj (rows r)).comp W.subtype
  have hcols : Submodule.span L (Set.range (exteriorFlattening W ω α rows columns).col) ≤
      U.map restriction := by
    apply Submodule.span_le.mpr
    rintro _ ⟨c, rfl⟩
    exact exteriorFlattening_column_mem W ω α rows columns U hω c
  calc
    (exteriorFlattening W ω α rows columns).rank =
        finrank L (Submodule.span L (Set.range (exteriorFlattening W ω α rows columns).col)) :=
      Matrix.rank_eq_finrank_span_cols _
    _ ≤ finrank L (U.map restriction) := Submodule.finrank_mono hcols
    _ ≤ finrank L U := Submodule.finrank_map_le restriction U
    _ = exteriorSupportDim ω := hdim

end AlternatingAnalytic
