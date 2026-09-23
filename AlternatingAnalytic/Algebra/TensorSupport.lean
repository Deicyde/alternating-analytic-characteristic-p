import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.LinearAlgebra.TensorPower.Basic

/-!
# Partial tensor contractions and mode supports

Contracting all factors except a selected one defines a linear map from a finite tensor
product to the selected factor. The covector at that factor is unused.
The mode support is the span of all such contraction values, using all algebraic covectors.
-/

open scoped TensorProduct

namespace AlternatingAnalytic

universe u v

section Family

variable (R : Type*) [CommSemiring R]
  {ι : Type*} [Fintype ι] (M : ι → Type*)
  [∀ j, AddCommMonoid (M j)] [∀ j, Module R (M j)]

/-- Contract every factor of a finite tensor product except the factor indexed by `i`.
The covector `φ i` is unused. -/
noncomputable def tensorContractionFamily (i : ι) (φ : ∀ j, Module.Dual R (M j)) :
    (⨂[R] j, M j) →ₗ[R] M i := by
  classical
  refine PiTensorProduct.lift (MultilinearMap.mk'
    (fun x ↦ (∏ j ∈ Finset.univ.erase i, φ j (x j)) • x i) ?_ ?_)
  · intro x j u v
    simp_rw [Function.apply_update (fun j ↦ (φ j : M j → R))]
    by_cases h : j = i
    · subst j
      simp [Finset.prod_update_of_notMem, smul_add]
    · have hj : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨h, Finset.mem_univ j⟩
      simp [Finset.prod_update_of_mem hj, Function.update_of_ne (Ne.symm h), add_mul, add_smul]
  · intro x j c u
    simp_rw [Function.apply_update (fun j ↦ (φ j : M j → R))]
    by_cases h : j = i
    · subst j
      simp only [Finset.prod_update_of_notMem (Finset.notMem_erase i _), Function.update_self]
      exact smul_comm _ _ _
    · have hj : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨h, Finset.mem_univ j⟩
      simp [Finset.prod_update_of_mem hj, Function.update_of_ne (Ne.symm h), mul_assoc,
        mul_smul]

@[simp]
theorem tensorContractionFamily_tprod [DecidableEq ι]
    (i : ι) (φ : ∀ j, Module.Dual R (M j)) (x : ∀ j, M j) :
    tensorContractionFamily R M i φ (PiTensorProduct.tprod R x) =
      (∏ j ∈ Finset.univ.erase i, φ j (x j)) • x i := by
  classical
  simp only [tensorContractionFamily, PiTensorProduct.lift.tprod, MultilinearMap.mk'_apply]
  congr 2
  ext j
  simp

/-- A coordinate of a partial contraction is the corresponding tensor coordinate. -/
theorem tensorContractionFamily_coord
    {I : ι → Type*} (b : ∀ j, Module.Basis (I j) R (M j)) (p : ∀ j, I j) (i : ι)
    (τ : ⨂[R] j, M j) :
    (b i).coord (p i)
      (tensorContractionFamily R M i (fun j ↦ (b j).coord (p j)) τ) =
      (Basis.piTensorProduct b).repr τ p := by
  classical
  have h : ((b i).coord (p i)).comp
      (tensorContractionFamily R M i (fun j ↦ (b j).coord (p j))) =
      (Basis.piTensorProduct b).coord p := by
    apply PiTensorProduct.ext
    ext x
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      tensorContractionFamily_tprod, map_smul, Module.Basis.coord_apply,
      Basis.piTensorProduct_repr_tprod_apply, smul_eq_mul]
    exact Finset.prod_erase_mul Finset.univ (fun j ↦ (b j).repr (x j) (p j))
      (Finset.mem_univ i)
  exact LinearMap.congr_fun h τ

/-- The support in one factor of a finite tensor product, defined as the span of all
partial contractions against algebraic covectors in the remaining factors. -/
noncomputable def tensorModeSupportFamily (τ : ⨂[R] j, M j) (i : ι) : Submodule R (M i) :=
  Submodule.span R
    (Set.range (fun φ : ∀ j, Module.Dual R (M j) ↦ tensorContractionFamily R M i φ τ))

theorem tensorModeSupportFamily_def (τ : ⨂[R] j, M j) (i : ι) :
    tensorModeSupportFamily R M τ i = Submodule.span R
      (Set.range (fun φ : ∀ j, Module.Dual R (M j) ↦ tensorContractionFamily R M i φ τ)) :=
  rfl

/-- Every partial contraction belongs to the support in the uncontracted factor. -/
theorem tensorContractionFamily_mem_tensorModeSupportFamily
    (τ : ⨂[R] j, M j) (i : ι) (φ : ∀ j, Module.Dual R (M j)) :
    tensorContractionFamily R M i φ τ ∈ tensorModeSupportFamily R M τ i :=
  Submodule.subset_span ⟨φ, rfl⟩

/-- The mode support of a scaled pure tensor lies in the span of its selected vector. -/
theorem tensorModeSupportFamily_smul_tprod_le (c : R) (x : ∀ j, M j) (i : ι) :
    tensorModeSupportFamily R M (c • PiTensorProduct.tprod R x) i ≤ R ∙ x i := by
  classical
  rw [tensorModeSupportFamily_def]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨φ, rfl⟩
  simp only [map_smul, tensorContractionFamily_tprod]
  exact Submodule.smul_mem _ _
    (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton (x i))))

/-- The mode support of a sum lies in the sum of the two mode supports. -/
theorem tensorModeSupportFamily_add_le (τ υ : ⨂[R] j, M j) (i : ι) :
    tensorModeSupportFamily R M (τ + υ) i ≤
      tensorModeSupportFamily R M τ i ⊔ tensorModeSupportFamily R M υ i := by
  rw [tensorModeSupportFamily_def]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨φ, rfl⟩
  simp only [map_add]
  exact Submodule.add_mem _
    (Submodule.mem_sup_left (tensorContractionFamily_mem_tensorModeSupportFamily R M τ i φ))
    (Submodule.mem_sup_right (tensorContractionFamily_mem_tensorModeSupportFamily R M υ i φ))

/-- A tensor realized in a family of submodules has all its mode supports in those
submodules. -/
theorem tensorModeSupportFamily_le_of_mem_range
    (W : ∀ j, Submodule R (M j)) (τ : ⨂[R] j, M j)
    (hτ : τ ∈ LinearMap.range (PiTensorProduct.mapIncl W)) (i : ι) :
    tensorModeSupportFamily R M τ i ≤ W i := by
  classical
  obtain ⟨υ, rfl⟩ := hτ
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨φ, rfl⟩
  induction υ using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    simp only [PiTensorProduct.mapIncl, map_smul, PiTensorProduct.map_tprod,
      tensorContractionFamily_tprod, Submodule.subtype_apply]
    exact (W i).smul_mem c ((W i).smul_mem _ (x i).property)
  | add υ ω hυ hω =>
    simpa only [map_add, SetLike.mem_coe] using (W i).add_mem hυ hω

end Family

/-- A basis adapted to a subspace: every nonzero coordinate of a vector in the
subspace belongs to a basis vector in that subspace. -/
private theorem exists_basis_adapted_to_submodule
    (L : Type u) [Field L] (M : Type v) [AddCommGroup M] [Module L M]
    (W : Submodule L M) :
    ∃ (I : Type v) (b : Module.Basis I L M),
      ∀ (x : M), x ∈ W → ∀ p, b.coord p x ≠ 0 → b p ∈ W := by
  classical
  obtain ⟨C, hC⟩ := W.exists_isCompl
  let bW := Module.Free.chooseBasis L W
  let bC := Module.Free.chooseBasis L C
  let e := W.prodEquivOfIsCompl C hC
  let b := (bW.prod bC).map e
  refine ⟨_, b, ?_⟩
  intro x hx p hp
  cases p with
  | inl j =>
    change e (bW.prod bC (Sum.inl j)) ∈ W
    simp [e, Module.Basis.prod_apply]
  | inr j =>
    have he : e.symm x = (⟨x, hx⟩, 0) :=
      W.prodEquivOfIsCompl_symm_apply_left C hC ⟨x, hx⟩
    have hz : b.coord (Sum.inr j) x = 0 := by
      change (bW.prod bC).repr (e.symm x) (Sum.inr j) = 0
      rw [he]
      simp
    exact (hp hz).elim

section VectorSpace

variable (L : Type*) [Field L]
  {ι : Type*} [Fintype ι] (M : ι → Type*)
  [∀ j, AddCommGroup (M j)] [∀ j, Module L (M j)]

/-- Every mode support of an algebraic tensor is finite-dimensional, even when its
ambient factor spaces are infinite-dimensional. -/
theorem tensorModeSupportFamily_finite (τ : ⨂[L] j, M j) (i : ι) :
    Module.Finite L (tensorModeSupportFamily L M τ i) := by
  induction τ using PiTensorProduct.induction_on with
  | smul_tprod c x =>
    exact Submodule.finiteDimensional_of_le (tensorModeSupportFamily_smul_tprod_le L M c x i)
  | add τ υ hτ hυ =>
    let := hτ
    let := hυ
    exact Submodule.finiteDimensional_of_le (tensorModeSupportFamily_add_le L M τ υ i)

/-- A tensor belongs to the tensor product of a family of subspaces exactly when
each mode support is contained in the corresponding subspace. -/
theorem tensorModeSupportFamily_le_iff
    (W : ∀ j, Submodule L (M j)) (τ : ⨂[L] j, M j) :
    τ ∈ LinearMap.range (PiTensorProduct.mapIncl W) ↔
      ∀ i, tensorModeSupportFamily L M τ i ≤ W i := by
  classical
  constructor
  · intro hτ i
    exact tensorModeSupportFamily_le_of_mem_range L M W τ hτ i
  · intro hτ
    choose I b hb using fun i ↦ exists_basis_adapted_to_submodule L (M i) (W i)
    let B := Basis.piTensorProduct b
    rw [← B.linearCombination_repr τ, Finsupp.linearCombination_apply, Finsupp.sum]
    refine Submodule.sum_mem _ fun p hp ↦ ?_
    refine Submodule.smul_mem _ _ ?_
    have hbp : ∀ i, b i (p i) ∈ W i := by
      intro i
      apply hb i (tensorContractionFamily L M i (fun j ↦ (b j).coord (p j)) τ)
        (hτ i (tensorContractionFamily_mem_tensorModeSupportFamily L M τ i _)) (p i)
      rw [tensorContractionFamily_coord]
      exact Finsupp.mem_support_iff.mp hp
    refine ⟨PiTensorProduct.tprod L (fun i ↦ ⟨b i (p i), hbp i⟩), ?_⟩
    simp [B]

/-- Every algebraic tensor is realized in the tensor product of its mode supports. -/
theorem mem_range_tensorModeSupportFamily (τ : ⨂[L] j, M j) :
    τ ∈ LinearMap.range (PiTensorProduct.mapIncl (tensorModeSupportFamily L M τ)) :=
  (tensorModeSupportFamily_le_iff L M _ τ).2 fun _ ↦ le_rfl

end VectorSpace

section TensorPower

variable (L : Type*) [Field L]
  {V : Type*} [AddCommGroup V] [Module L V] {k : ℕ}

/-- Partial contraction of a tensor power, leaving its `i`-th vector factor uncontracted. -/
noncomputable def tensorContraction (i : Fin k) (φ : Fin k → Module.Dual L V) :
    (⨂[L]^k V) →ₗ[L] V :=
  tensorContractionFamily L (fun _ : Fin k ↦ V) i φ

@[simp]
theorem tensorContraction_tprod (i : Fin k) (φ : Fin k → Module.Dual L V)
    (x : Fin k → V) :
    tensorContraction L i φ (PiTensorProduct.tprod L x) =
      (∏ j ∈ Finset.univ.erase i, φ j (x j)) • x i :=
  tensorContractionFamily_tprod L (fun _ : Fin k ↦ V) i φ x

variable {L}

/-- The intrinsic support of a tensor power in its `i`-th factor: the span of all
partial contractions against algebraic covectors. -/
noncomputable def tensorModeSupport (τ : ⨂[L]^k V) (i : Fin k) : Submodule L V :=
  tensorModeSupportFamily L (fun _ : Fin k ↦ V) τ i

theorem tensorModeSupport_def (τ : ⨂[L]^k V) (i : Fin k) :
    tensorModeSupport τ i = Submodule.span L
      (Set.range (fun φ : Fin k → Module.Dual L V ↦ tensorContraction L i φ τ)) :=
  rfl

/-- Every partial contraction belongs to the corresponding tensor mode support. -/
theorem tensorContraction_mem_tensorModeSupport
    (τ : ⨂[L]^k V) (i : Fin k) (φ : Fin k → Module.Dual L V) :
    tensorContraction L i φ τ ∈ tensorModeSupport τ i :=
  tensorContractionFamily_mem_tensorModeSupportFamily L (fun _ : Fin k ↦ V) τ i φ

/-- Every mode support of an algebraic tensor power is finite-dimensional. -/
theorem tensorModeSupport_finite (τ : ⨂[L]^k V) (i : Fin k) :
    Module.Finite L (tensorModeSupport τ i) :=
  tensorModeSupportFamily_finite L (fun _ : Fin k ↦ V) τ i

/-- A tensor power is realized in a family of subspaces exactly when its mode supports
are contained in those subspaces. -/
theorem tensorModeSupport_le_iff (W : Fin k → Submodule L V) (τ : ⨂[L]^k V) :
    τ ∈ LinearMap.range (PiTensorProduct.mapIncl W) ↔
      ∀ i, tensorModeSupport τ i ≤ W i :=
  tensorModeSupportFamily_le_iff L (fun _ : Fin k ↦ V) W τ

/-- A tensor power is realized in the tensor product of its mode supports. -/
theorem mem_range_tensorModeSupport (τ : ⨂[L]^k V) :
    τ ∈ LinearMap.range (PiTensorProduct.mapIncl (tensorModeSupport τ)) :=
  (tensorModeSupport_le_iff _ τ).2 fun _ ↦ le_rfl

end TensorPower

end AlternatingAnalytic
