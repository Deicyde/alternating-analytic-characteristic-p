import AlternatingAnalytic.Algebra.ExteriorContraction
import AlternatingAnalytic.Algebra.ExteriorSupport
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.LinearAlgebra.Dual.Basis

/-!
# Canonical exterior support

Over any field, the span of the algebraic contractions of an exterior vector is
its smallest supporting subspace. Antisymmetrization places the vector in the
tensor product of its contraction span; an algebraic retraction and injectivity
of antisymmetrization then recover exterior support, without dividing by a
factorial. The positive-degree statements include degree one. Degree zero is
handled separately, and finite coordinate contraction matrices compute the
support dimension.
-/

namespace AlternatingAnalytic

open Module

variable {L : Type*} [Field L]
  {V : Type*} [AddCommGroup V] [Module L V] {n : ℕ}

/-- Moving the uncontracted slot to the last position contributes its cofactor sign. -/
theorem exteriorContraction_eq_sign_smul_last
    (α : Fin (n + 1)) (φ : Fin (n + 1) → Dual L V) :
    exteriorContraction α φ =
      (-1 : L) ^ (n + α.val) •
        exteriorLastContraction (fun j : Fin n => φ (α.succAbove j)) := by
  apply exteriorPower.linearMap_ext
  ext x
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.smul_apply,
    exteriorContraction_ιMulti, exteriorLastContraction_ιMulti, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro i hi
  have hs : (-1 : L) ^ (n + α.val) * (-1 : L) ^ (n + i.val) =
      (-1 : L) ^ (α.val + i.val) := by
    rw [← pow_add, show n + α.val + (n + i.val) = 2 * n + (α.val + i.val) by omega,
      pow_add, pow_mul]
    simp
  rw [← mul_assoc, hs]

/-- Every tensor mode support of an exterior vector lies in its contraction span. -/
theorem tensorModeSupport_toTensorPower_le_contractionSpan
    (ω : ⋀[L]^(n + 1) V) (α : Fin (n + 1)) :
    tensorModeSupport (exteriorPower.toTensorPower L V (n + 1) ω) α ≤
      exteriorContractionSpan ω := by
  rw [tensorModeSupport_def]
  apply Submodule.span_le.mpr
  rintro _ ⟨φ, rfl⟩
  change exteriorContraction α φ ω ∈ exteriorContractionSpan ω
  rw [exteriorContraction_eq_sign_smul_last, LinearMap.smul_apply]
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨fun j => φ (α.succAbove j), rfl⟩

/-- Antisymmetrization commutes with every linear map. -/
theorem toTensorPower_map
    {V' : Type*} [AddCommGroup V'] [Module L V'] {k : ℕ}
    (f : V →ₗ[L] V') (ω : ⋀[L]^k V) :
    exteriorPower.toTensorPower L V' k (exteriorPower.map k f ω) =
      PiTensorProduct.map (fun _ : Fin k => f)
        (exteriorPower.toTensorPower L V k ω) := by
  have h : (exteriorPower.toTensorPower L V' k).comp (exteriorPower.map k f) =
      (PiTensorProduct.map (fun _ : Fin k => f)).comp
        (exteriorPower.toTensorPower L V k) := by
    apply exteriorPower.linearMap_ext
    ext x
    simp [exteriorPower.toTensorPower_apply_ιMulti]
  exact LinearMap.congr_fun h ω

/-- Contracting a degree-one exterior vector uses no covectors. -/
theorem exteriorLastContraction_zero
    (φ : Fin 0 → Dual L V) (ω : ⋀[L]^1 V) :
    exteriorLastContraction φ ω = exteriorPower.oneEquiv L V ω := by
  have h : exteriorLastContraction φ = (exteriorPower.oneEquiv L V).toLinearMap := by
    apply exteriorPower.linearMap_ext
    ext x
    simp only [Nat.reduceAdd, LinearMap.compAlternatingMap_apply, LinearEquiv.coe_coe,
      exteriorLastContraction_ιMulti, exteriorPower.oneEquiv_ιMulti,
      Fin.sum_univ_one, Fin.val_zero, Nat.zero_add, pow_zero, one_mul]
    erw [Matrix.det_fin_zero]
    exact one_smul L (x 0)
  exact LinearMap.congr_fun h ω

/-- The canonical support in degree one is the line spanned by the vector. -/
theorem exteriorContractionSpan_one (ω : ⋀[L]^1 V) :
    exteriorContractionSpan ω =
      Submodule.span L {exteriorPower.oneEquiv L V ω} := by
  simp [exteriorContractionSpan, exteriorLastContraction_zero]

/-- Every degree-zero exterior vector is supported on the zero subspace. -/
theorem mem_exteriorPowerSubmodule_zero (ω : ⋀[L]^0 V) :
    ω ∈ exteriorPowerSubmodule 0 (⊥ : Submodule L V) := by
  refine ⟨(exteriorPower.zeroEquiv L (⊥ : Submodule L V)).symm
    (exteriorPower.zeroEquiv L V ω), ?_⟩
  apply (exteriorPower.zeroEquiv L V).injective
  have h := LinearMap.congr_fun
    (exteriorPower.zeroEquiv_naturality (⊥ : Submodule L V).subtype)
    ((exteriorPower.zeroEquiv L (⊥ : Submodule L V)).symm
      (exteriorPower.zeroEquiv L V ω))
  simpa using h

/-- Scalars have support dimension zero, including nonzero scalars. -/
theorem exteriorSupportDim_degree_zero (ω : ⋀[L]^0 V) :
    exteriorSupportDim ω = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa using exteriorSupportDim_le_finrank (⊥ : Submodule L V)
    (mem_exteriorPowerSubmodule_zero ω)

/-- An exterior vector is supported on the span of all its last-slot contractions. -/
theorem mem_exteriorPowerSubmodule_contractionSpan
    (ω : ⋀[L]^(n + 1) V) :
    ω ∈ exteriorPowerSubmodule (n + 1) (exteriorContractionSpan ω) := by
  let W := exteriorContractionSpan ω
  obtain ⟨q, hq⟩ := W.subtype.exists_leftInverse_of_injective W.ker_subtype
  have hτ : exteriorPower.toTensorPower L V (n + 1) ω ∈
      LinearMap.range (PiTensorProduct.mapIncl (fun _ : Fin (n + 1) ↦ W)) :=
    (tensorModeSupport_le_iff _ _).2
      (tensorModeSupport_toTensorPower_le_contractionSpan ω)
  have hfix : PiTensorProduct.map (fun _ : Fin (n + 1) ↦ W.subtype.comp q)
      (exteriorPower.toTensorPower L V (n + 1) ω) =
      exteriorPower.toTensorPower L V (n + 1) ω := by
    obtain ⟨υ, hυ⟩ := hτ
    rw [← hυ]
    have hr : (W.subtype.comp q).comp W.subtype = W.subtype := by
      rw [LinearMap.comp_assoc, hq, LinearMap.comp_id]
    change PiTensorProduct.map (fun _ : Fin (n + 1) ↦ W.subtype.comp q)
        (PiTensorProduct.map (fun _ : Fin (n + 1) ↦ W.subtype) υ) = _
    rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
    simp only [hr, PiTensorProduct.mapIncl]
  refine ⟨exteriorPower.map (n + 1) q ω, ?_⟩
  change exteriorPower.map (n + 1) W.subtype (exteriorPower.map (n + 1) q ω) = ω
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
  apply toTensorPower_injective L V (n + 1)
  rw [toTensorPower_map]
  exact hfix

/-- A subspace supports an exterior vector exactly when it contains its contraction span. -/
theorem mem_exteriorPowerSubmodule_iff_contractionSpan_le
    (W : Submodule L V) (ω : ⋀[L]^(n + 1) V) :
    ω ∈ exteriorPowerSubmodule (n + 1) W ↔
      exteriorContractionSpan ω ≤ W := by
  constructor
  · exact exteriorContractionSpan_le W
  · intro h
    exact exteriorPowerSubmodule_mono h (mem_exteriorPowerSubmodule_contractionSpan ω)

/-- Exterior support dimension is the dimension of the actual contraction span. -/
theorem exteriorSupportDim_eq_finrank_contractionSpan
    (ω : ⋀[L]^(n + 1) V) :
    exteriorSupportDim ω = finrank L (exteriorContractionSpan ω) := by
  let := exteriorContractionSpan_finite ω
  exact le_antisymm
    (exteriorSupportDim_le_finrank _ (mem_exteriorPowerSubmodule_contractionSpan ω))
    (exteriorContractionSpan_finrank_le ω)

/-- The contraction span is the smallest supporting subspace, and its dimension
is the exterior support dimension, over any field and in every positive degree. -/
theorem canonical_exterior_support_full (ω : ⋀[L]^(n + 1) V) :
    ω ∈ exteriorPowerSubmodule (n + 1) (exteriorContractionSpan ω) ∧
      (∀ W : Submodule L V,
        ω ∈ exteriorPowerSubmodule (n + 1) W ↔ exteriorContractionSpan ω ≤ W) ∧
      exteriorSupportDim ω = finrank L (exteriorContractionSpan ω) := by
  exact ⟨mem_exteriorPowerSubmodule_contractionSpan ω,
    fun W ↦ mem_exteriorPowerSubmodule_iff_contractionSpan_le W ω,
    exteriorSupportDim_eq_finrank_contractionSpan ω⟩

/-- Expand a contraction into contractions against tuples of coordinate covectors. -/
theorem exteriorLastContraction_eq_sum_basis {d : ℕ} (b : Basis (Fin d) L V)
    (φ : Fin n → Dual L V) (ω : ⋀[L]^(n + 1) V) :
    exteriorLastContraction φ ω =
      ∑ a : Fin n → Fin d, (∏ j, φ j (b (a j))) •
        exteriorLastContraction (fun j ↦ b.coord (a j)) ω := by
  classical
  apply b.eval_injective
  ext ψ
  let F := (exteriorPower.alternatingMapToDual L V (n + 1)).toMultilinearMap.curryRight
  have heval (θ : Fin n → Dual L V) :
      ψ (exteriorLastContraction θ ω) = F θ ψ ω := by
    rw [exteriorLastContraction, exteriorContraction_eval]
    change exteriorPower.alternatingMapToDual L V (n + 1)
      (Function.update (Fin.lastCases 0 θ) (Fin.last n) ψ) ω =
      exteriorPower.alternatingMapToDual L V (n + 1) (Fin.snoc θ ψ) ω
    apply congrArg (fun η ↦ exteriorPower.alternatingMapToDual L V (n + 1) η ω)
    funext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i <;>
      simp [Fin.snoc]
  change ψ _ = ψ _
  rw [heval]
  have hφ : φ = (fun j ↦ ∑ i : Fin d, φ j (b i) • b.coord i) := by
    funext j
    exact (b.sum_dual_apply_smul_coord (φ j)).symm
  conv_lhs => rw [hφ, F.map_sum]
  simp only [MultilinearMap.map_smul_univ, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul, smul_eq_mul, heval]

/-- Coordinate covectors already generate the entire contraction span. -/
theorem exteriorContractionSpan_eq_span_basis {d : ℕ} (b : Basis (Fin d) L V)
    (ω : ⋀[L]^(n + 1) V) :
    exteriorContractionSpan ω = Submodule.span L
      (Set.range (fun a : Fin n → Fin d ↦
        exteriorLastContraction (fun j ↦ b.coord (a j)) ω)) := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨φ, rfl⟩
    dsimp only
    rw [exteriorLastContraction_eq_sum_basis b]
    exact Submodule.sum_mem _ (fun a _ ↦ Submodule.smul_mem _ _
      (Submodule.subset_span ⟨a, rfl⟩))
  · apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact Submodule.subset_span ⟨fun j ↦ b.coord (a j), rfl⟩

/-- The matrix of coordinate contractions has rank equal to the dimension of the
contraction span. -/
theorem rank_exteriorContractionMatrix_eq_finrank {d : ℕ} (b : Basis (Fin d) L V)
    (ω : ⋀[L]^(n + 1) V) :
    Matrix.rank (Matrix.of (fun (i : Fin d) (a : Fin n → Fin d) ↦
      b.coord i (exteriorLastContraction (fun j ↦ b.coord (a j)) ω))) =
        finrank L (exteriorContractionSpan ω) := by
  classical
  rw [Matrix.rank_eq_finrank_span_cols]
  have hspan : Submodule.span L (Set.range
      (fun a : Fin n → Fin d ↦ fun i : Fin d ↦
        b.coord i (exteriorLastContraction (fun j ↦ b.coord (a j)) ω))) =
      (exteriorContractionSpan ω).map b.equivFun.toLinearMap := by
    rw [exteriorContractionSpan_eq_span_basis b, Submodule.map_span]
    congr 1
    rw [← Set.range_comp]
    rfl
  change finrank L (Submodule.span L (Set.range
    (fun a : Fin n → Fin d ↦ fun i : Fin d ↦
      b.coord i (exteriorLastContraction (fun j ↦ b.coord (a j)) ω)))) = _
  rw [hspan]
  exact b.equivFun.finrank_map_eq _

/-- A finite coordinate contraction matrix computes exterior support dimension. -/
theorem rank_exteriorContractionMatrix
    {d : ℕ} (b : Basis (Fin d) L V) (ω : ⋀[L]^(n + 1) V) :
    Matrix.rank (Matrix.of (fun (i : Fin d) (a : Fin n → Fin d) ↦
      b.coord i (exteriorLastContraction (fun j ↦ b.coord (a j)) ω))) =
        exteriorSupportDim ω := by
  rw [rank_exteriorContractionMatrix_eq_finrank,
    exteriorSupportDim_eq_finrank_contractionSpan]

end AlternatingAnalytic
