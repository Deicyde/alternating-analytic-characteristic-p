/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
import AlternatingAnalytic.Analysis.SphericalCompleteness
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSeminorm
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# Ordinary projective scalar extension

Scalar functionals act on the second factor of the actual algebraic tensor product.
Their separation property is obtained on finite-dimensional scalar subspaces and extended
by Ingleton; it requires no continuous linear functional on the original space.

This is the ordinary projective base-change construction in `sources/charp.tex`,
Lemma `bc`, parts (1) and (2). The original normed space need not be complete or ultrametric.
-/

open scoped TensorProduct

namespace AlternatingAnalytic

section Contraction

variable {K V L : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup L] [Module K L]

/-- Apply a scalar functional to the second tensor factor. -/
def scalarContraction (ψ : L →ₗ[K] K) : V ⊗[K] L →ₗ[K] V :=
  (TensorProduct.rid K V).toLinearMap.comp (ψ.lTensor V)

@[simp]
theorem scalarContraction_tmul (ψ : L →ₗ[K] K) (v : V) (l : L) :
    scalarContraction ψ (v ⊗ₜ[K] l) = ψ l • v := by
  simp [scalarContraction]

end Contraction

section FiniteDimensionalExtension

variable {K L : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  [IsUltrametricDist K] [SphericallyCompleteSpace K]
  [NormedAddCommGroup L] [NormedSpace K L] [IsUltrametricDist L]

/-- A functional on a finite-dimensional scalar subspace extends continuously to the
ultrametric ambient space. Completeness is needed only for the scalar field. -/
theorem exists_continuous_extension_of_finiteDimensional
    (D : Submodule K L) [FiniteDimensional K D] (φ : D →ₗ[K] K) :
    ∃ ψ : L →L[K] K, ∀ d : D, ψ d = φ d := by
  let φL : D →L[K] K := φ.toContinuousLinearMap
  obtain ⟨ψ, hψ, -⟩ := exists_extension_of_sphericallyComplete
    ({((0 : L →L[K] K), ‖φL‖)} : Set ((L →L[K] K) × ℝ))
    (Set.singleton_nonempty _)
    (by
      rintro p hp q hq
      rcases Set.mem_singleton_iff.mp hp with rfl
      rcases Set.mem_singleton_iff.mp hq with rfl
      simp)
    D φ (by
      rintro p hp d
      rcases Set.mem_singleton_iff.mp hp with rfl
      change ‖φL d - 0‖ ≤ ‖φL‖ * ‖(d : L)‖
      simpa only [sub_zero, Submodule.norm_coe] using φL.le_opNorm d)
  exact ⟨ψ, hψ⟩

/-- Continuous scalar functionals separate the second factor of an algebraic tensor product.
No topology or continuous dual on `V` is used. -/
theorem exists_scalarContraction_ne_zero {V : Type*} [AddCommGroup V] [Module K V]
    (u : V ⊗[K] L) (hu : u ≠ 0) :
    ∃ ψ : L →L[K] K, scalarContraction ψ.toLinearMap u ≠ 0 := by
  classical
  obtain ⟨D, hD, hmem⟩ := TensorProduct.exists_finite_submodule_right_of_setFinite
    ({u} : Set (V ⊗[K] L)) (Set.finite_singleton u)
  let : FiniteDimensional K D := hD
  obtain ⟨w, hw⟩ := hmem (Set.mem_singleton u)
  have hw0 : w ≠ 0 := by
    intro h
    apply hu
    rw [← hw, h, map_zero]
  let b := Module.Free.chooseBasis K D
  let e := TensorProduct.equivFinsuppOfBasisRight (M := V) b
  have hew : e w ≠ 0 := by
    intro h
    exact hw0 (e.injective (h.trans (map_zero e).symm))
  obtain ⟨j, hj⟩ := Finsupp.ne_iff.mp hew
  obtain ⟨ψ, hψ⟩ := exists_continuous_extension_of_finiteDimensional D (b.coord j)
  refine ⟨ψ, ?_⟩
  have hdetect : scalarContraction ψ.toLinearMap u = e w j := by
    rw [← hw]
    change scalarContraction ψ.toLinearMap (D.subtype.lTensor V w) =
      TensorProduct.equivFinsuppOfBasisRight b w j
    rw [TensorProduct.equivFinsuppOfBasisRight_apply]
    clear hw hw0 hew hj
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul v d => simp [hψ d]
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  rw [hdetect]
  exact hj

end FiniteDimensionalExtension

section ProjectiveSeminorm

universe u

variable (K : Type*) (V L : Type u) [NontriviallyNormedField K]
  [NormedAddCommGroup V] [NormedSpace K V]
  [NormedAddCommGroup L] [NormedSpace K L]

/-- The two factors of algebraic scalar extension, indexed by a two-element sum. -/
abbrev baseChangeFactors : Unit ⊕ Unit → Type _
  | .inl _ => V
  | .inr _ => L

@[reducible]
instance baseChangeFactorsNormedAddCommGroup (i : Unit ⊕ Unit) :
    NormedAddCommGroup (baseChangeFactors V L i) :=
  match i with
  | .inl _ => inferInstanceAs (NormedAddCommGroup V)
  | .inr _ => inferInstanceAs (NormedAddCommGroup L)

@[reducible]
instance baseChangeFactorsNormedSpace (i : Unit ⊕ Unit) :
    NormedSpace K (baseChangeFactors V L i) :=
  match i with
  | .inl _ => inferInstanceAs (NormedSpace K V)
  | .inr _ => inferInstanceAs (NormedSpace K L)

/-- Identify the binary algebraic tensor product with the tensor of its two factors. -/
noncomputable def baseChangeTensorEquiv :
    V ⊗[K] L ≃ₗ[K] (⨂[K] i, baseChangeFactors V L i) :=
  (TensorProduct.congr
    (PiTensorProduct.subsingletonEquiv (R := K) (s := fun _ : Unit => V) ()).symm
    (PiTensorProduct.subsingletonEquiv (R := K) (s := fun _ : Unit => L) ()).symm).trans
    (PiTensorProduct.tmulEquivDep K (baseChangeFactors V L))

@[simp]
theorem baseChangeTensorEquiv_tmul (v : V) (l : L) :
    baseChangeTensorEquiv K V L (v ⊗ₜ[K] l) =
      PiTensorProduct.tprod K (Sum.rec (fun _ : Unit => v) (fun _ : Unit => l)) := by
  simp [baseChangeTensorEquiv, LinearEquiv.trans_apply]

@[simp]
theorem baseChangeTensorEquiv_symm_tprod (f : ∀ i, baseChangeFactors V L i) :
    (baseChangeTensorEquiv K V L).symm (PiTensorProduct.tprod K f) =
      f (.inl ()) ⊗ₜ[K] f (.inr ()) := by
  simp [baseChangeTensorEquiv, LinearEquiv.trans_apply]

theorem baseChangeFactors_prod_norm (f : ∀ i, baseChangeFactors V L i) :
    (∏ i, ‖f i‖) = ‖f (.inl ())‖ * ‖f (.inr ())‖ := by
  simp [Fintype.prod_sum_type]

/-- The ordinary sum projective seminorm on the actual binary tensor product. It is the
pullback of Mathlib's finite-decomposition projective seminorm, not an ultrametric maximum. -/
noncomputable def baseChangeSeminorm : Seminorm K (V ⊗[K] L) :=
  PiTensorProduct.projectiveSeminorm.comp (baseChangeTensorEquiv K V L).toLinearMap

theorem baseChangeSeminorm_apply (u : V ⊗[K] L) :
    baseChangeSeminorm K V L u = ‖baseChangeTensorEquiv K V L u‖ := rfl

theorem baseChangeSeminorm_tmul_le (v : V) (l : L) :
    baseChangeSeminorm K V L (v ⊗ₜ[K] l) ≤ ‖v‖ * ‖l‖ := by
  rw [baseChangeSeminorm_apply, baseChangeTensorEquiv_tmul]
  have h := PiTensorProduct.projectiveSeminorm_tprod_le
    (𝕜 := K) (E := baseChangeFactors V L)
    (Sum.rec (fun _ : Unit => v) (fun _ : Unit => l))
  rw [baseChangeFactors_prod_norm] at h
  exact h

/-- A finite decomposition into binary pure tensors. -/
def BaseChangeDecomposition (u : V ⊗[K] L) :=
  {s : List (V × L) // (s.map fun z => z.1 ⊗ₜ[K] z.2).sum = u}

/-- Absorb each coefficient in a projective lift into its first factor. -/
def baseChangeLiftTerms (p : FreeAddMonoid (K × ∀ i, baseChangeFactors V L i)) :
    List (V × L) :=
  p.toList.map fun z => (z.1 • z.2 (.inl ()), z.2 (.inr ()))

theorem baseChangeLiftTerms_sum (u : V ⊗[K] L)
    (p : PiTensorProduct.lifts (baseChangeTensorEquiv K V L u)) :
    ((baseChangeLiftTerms K V L p.val).map fun z => z.1 ⊗ₜ[K] z.2).sum = u := by
  have h := congrArg (baseChangeTensorEquiv K V L).symm
    ((PiTensorProduct.mem_lifts_iff _ _).mp p.property)
  simpa only [baseChangeLiftTerms, map_list_sum, List.map_map, Function.comp_def,
    map_smul, baseChangeTensorEquiv_symm_tprod, TensorProduct.smul_tmul',
    LinearEquiv.symm_apply_apply] using h

omit [NormedSpace K L] in
theorem baseChangeLiftTerms_cost (p : FreeAddMonoid (K × ∀ i, baseChangeFactors V L i)) :
    ((baseChangeLiftTerms K V L p).map fun z => ‖z.1‖ * ‖z.2‖).sum =
      PiTensorProduct.projectiveSeminormAux p := by
  simp only [baseChangeLiftTerms, PiTensorProduct.projectiveSeminormAux, List.map_map,
    Function.comp_def, baseChangeFactors_prod_norm, norm_smul, mul_assoc]

instance baseChangeDecompositionNonempty (u : V ⊗[K] L) :
    Nonempty (BaseChangeDecomposition K V L u) := by
  obtain ⟨p, hp⟩ := PiTensorProduct.nonempty_lifts (baseChangeTensorEquiv K V L u)
  exact ⟨⟨baseChangeLiftTerms K V L p, baseChangeLiftTerms_sum K V L u ⟨p, hp⟩⟩⟩

theorem baseChangeSeminorm_list_sum_le (s : List (V × L)) :
    baseChangeSeminorm K V L (s.map fun z => z.1 ⊗ₜ[K] z.2).sum ≤
      (s.map fun z => ‖z.1‖ * ‖z.2‖).sum := by
  induction s with
  | nil => simp
  | cons z s ih =>
    simp only [List.map_cons, List.sum_cons]
    change ‖baseChangeTensorEquiv K V L
      ((z.1 ⊗ₜ[K] z.2) + (s.map fun z => z.1 ⊗ₜ[K] z.2).sum)‖ ≤ _
    rw [map_add]
    exact (norm_add_le _ _).trans
      (add_le_add (baseChangeSeminorm_tmul_le K V L z.1 z.2) ih)

/-- The defining infimum is over ordinary finite sums of products of norms. -/
theorem baseChangeSeminorm_eq_iInf (u : V ⊗[K] L) :
    baseChangeSeminorm K V L u =
      ⨅ s : BaseChangeDecomposition K V L u, (s.val.map fun z => ‖z.1‖ * ‖z.2‖).sum := by
  have hbdd : BddBelow (Set.range (fun s : BaseChangeDecomposition K V L u =>
      (s.val.map fun z => ‖z.1‖ * ‖z.2‖).sum)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨s, rfl⟩
    apply List.sum_nonneg
    intro x hx
    obtain ⟨⟨v, l⟩, _, rfl⟩ := List.mem_map.mp hx
    exact mul_nonneg (norm_nonneg v) (norm_nonneg l)
  refine le_antisymm (le_ciInf fun s => ?_) ?_
  · simpa only [s.property] using baseChangeSeminorm_list_sum_le K V L s.val
  · rw [baseChangeSeminorm_apply, PiTensorProduct.norm_def]
    refine le_ciInf fun p => ?_
    exact ciInf_le_of_le hbdd
      ⟨baseChangeLiftTerms K V L p.val, baseChangeLiftTerms_sum K V L u p⟩
      (baseChangeLiftTerms_cost K V L p.val).le

variable {K V L}

/-- A bound on pure tensors extends with the same constant to the ordinary projective seminorm. -/
theorem norm_le_baseChangeSeminorm {G : Type*} [SeminormedAddCommGroup G]
    [NormedSpace K G] (f : V ⊗[K] L →ₗ[K] G) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ v l, ‖f (v ⊗ₜ[K] l)‖ ≤ C * (‖v‖ * ‖l‖)) (u : V ⊗[K] L) :
    ‖f u‖ ≤ C * baseChangeSeminorm K V L u := by
  let e := baseChangeTensorEquiv K V L
  let g : MultilinearMap K (baseChangeFactors V L) G :=
    PiTensorProduct.lift.symm (f.comp e.symm.toLinearMap)
  have hg : ∀ m, ‖g m‖ ≤ C * ∏ i, ‖m i‖ := by
    intro m
    change ‖f (e.symm (PiTensorProduct.tprod K m))‖ ≤ _
    rw [baseChangeFactors_prod_norm]
    simpa only [e, baseChangeTensorEquiv_symm_tprod] using
      hf (m (.inl ())) (m (.inr ()))
  let gC := g.mkContinuous C hg
  have hnorm : ‖gC‖ ≤ C := MultilinearMap.mkContinuous_norm_le g hC hg
  have h := PiTensorProduct.norm_eval_le_projectiveSeminorm gC (e u)
  have heval : PiTensorProduct.lift gC.toMultilinearMap (e u) = f u := by
    change PiTensorProduct.lift (PiTensorProduct.lift.symm
      (f.comp e.symm.toLinearMap)) (e u) = f u
    rw [LinearEquiv.apply_symm_apply]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rw [heval] at h
  exact h.trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))

/-- Scalar contraction is bounded for the ordinary sum projective seminorm. -/
theorem norm_scalarContraction_le (ψ : L →L[K] K) (u : V ⊗[K] L) :
    ‖scalarContraction ψ.toLinearMap u‖ ≤ ‖ψ‖ * baseChangeSeminorm K V L u := by
  apply norm_le_baseChangeSeminorm _ (norm_nonneg ψ) _ u
  intro v l
  simp only [scalarContraction_tmul, ContinuousLinearMap.coe_coe, norm_smul]
  calc
    ‖ψ l‖ * ‖v‖ ≤ (‖ψ‖ * ‖l‖) * ‖v‖ :=
      mul_le_mul_of_nonneg_right (ψ.le_opNorm l) (norm_nonneg v)
    _ = ‖ψ‖ * (‖v‖ * ‖l‖) := by ring

variable [CompleteSpace K] [IsUltrametricDist K] [SphericallyCompleteSpace K]
  [IsUltrametricDist L]

/-- Positivity uses coordinates on a finite-dimensional subspace of the scalar factor. -/
theorem baseChangeSeminorm_eq_zero_iff (u : V ⊗[K] L) :
    baseChangeSeminorm K V L u = 0 ↔ u = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  by_contra hu
  obtain ⟨ψ, hψ⟩ := exists_scalarContraction_ne_zero u hu
  have hbound := norm_scalarContraction_le ψ u
  rw [h, mul_zero] at hbound
  exact hψ (norm_eq_zero.mp (le_antisymm hbound (norm_nonneg _)))

theorem baseChangeSeminorm_pos (u : V ⊗[K] L) (hu : u ≠ 0) :
    0 < baseChangeSeminorm K V L u :=
  lt_of_le_of_ne (apply_nonneg _ u) (Ne.symm (mt (baseChangeSeminorm_eq_zero_iff u).mp hu))

end ProjectiveSeminorm

section ExtensionScalars

universe u

variable (K : Type*) (V L : Type u) [NontriviallyNormedField K]
  [NormedAddCommGroup V] [NormedSpace K V] [NormedField L] [NormedAlgebra K L]

/-- The extension-field module structure on the actual algebraic tensor product,
transported through the swap so that scalars act on the second factor. -/
@[instance_reducible]
noncomputable def baseChangeModule : Module L (V ⊗[K] L) :=
  (TensorProduct.comm K V L).toAddEquiv.module L

attribute [local instance] baseChangeModule

@[simp]
theorem baseChange_smul_tmul (a : L) (v : V) (l : L) :
    a • (v ⊗ₜ[K] l) = v ⊗ₜ[K] (a * l) := by
  change (TensorProduct.comm K V L).symm
    (a • (TensorProduct.comm K V L) (v ⊗ₜ[K] l)) = _
  simp [TensorProduct.smul_tmul']

/-- Multiplication on the scalar factor, as a linear map over the original field. -/
def baseChangeScalarMap (a : L) : V ⊗[K] L →ₗ[K] V ⊗[K] L :=
  (LinearMap.mulLeft K a).lTensor V

@[simp]
theorem baseChangeScalarMap_tmul (a : L) (v : V) (l : L) :
    baseChangeScalarMap K V L a (v ⊗ₜ[K] l) = v ⊗ₜ[K] (a * l) := by
  simp [baseChangeScalarMap]

theorem baseChangeScalarMap_apply (a : L) (u : V ⊗[K] L) :
    baseChangeScalarMap K V L a u = a • u := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul v l => simp
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]

theorem baseChangeSeminorm_smul_le (a : L) (u : V ⊗[K] L) :
    baseChangeSeminorm K V L (a • u) ≤ ‖a‖ * baseChangeSeminorm K V L u := by
  have h := norm_le_baseChangeSeminorm
    ((baseChangeTensorEquiv K V L).toLinearMap.comp (baseChangeScalarMap K V L a))
    (norm_nonneg a) (fun v l => ?_) u
  · simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      baseChangeScalarMap_apply, ← baseChangeSeminorm_apply] using h
  · change baseChangeSeminorm K V L (v ⊗ₜ[K] (a * l)) ≤ _
    calc
      _ ≤ ‖v‖ * ‖a * l‖ := baseChangeSeminorm_tmul_le K V L v (a * l)
      _ = ‖a‖ * (‖v‖ * ‖l‖) := by rw [norm_mul]; ring

/-- The same ordinary-sum seminorm is homogeneous over the extension field. -/
noncomputable def baseChangeSeminormL : Seminorm L (V ⊗[K] L) :=
  Seminorm.ofSMulLE (baseChangeSeminorm K V L) (map_zero _)
    (map_add_le_add _) (baseChangeSeminorm_smul_le K V L)

theorem baseChangeSeminorm_smul (a : L) (u : V ⊗[K] L) :
    baseChangeSeminorm K V L (a • u) = ‖a‖ * baseChangeSeminorm K V L u :=
  map_smul_eq_mul (baseChangeSeminormL K V L) a u

variable [CompleteSpace K] [IsUltrametricDist K] [SphericallyCompleteSpace K]
  [IsUltrametricDist L]

/-- The projective seminorm is a genuine additive group norm on the algebraic tensor product. -/
noncomputable def baseChangeNorm : AddGroupNorm (V ⊗[K] L) where
  __ := (baseChangeSeminorm K V L).toAddGroupSeminorm
  eq_zero_of_map_eq_zero' u hu := (baseChangeSeminorm_eq_zero_iff u).mp hu

/-- The normed additive group structure induced by the ordinary-sum projective norm. -/
@[instance_reducible]
noncomputable def baseChangeNormedAddCommGroup : NormedAddCommGroup (V ⊗[K] L) :=
  (baseChangeNorm K V L).toNormedAddCommGroup

/-- Projective scalar extension is a normed space over the extension field. -/
@[instance_reducible]
noncomputable def baseChangeNormedSpace :
    letI := baseChangeNormedAddCommGroup K V L
    NormedSpace L (V ⊗[K] L) := by
  letI := baseChangeNormedAddCommGroup K V L
  exact { baseChangeModule K V L with
    norm_smul_le := fun a u => (baseChangeSeminorm_smul K V L a u).le }

omit [CompleteSpace K] [IsUltrametricDist K] [SphericallyCompleteSpace K]
  [IsUltrametricDist L] in
/-- The original scalar action is compatible with the extension-field action. -/
theorem baseChangeIsScalarTower : IsScalarTower K L (V ⊗[K] L) :=
  LinearEquiv.isScalarTower L (TensorProduct.comm K V L)

/-- The projective norm also gives the original-field normed space structure. -/
@[instance_reducible]
noncomputable def baseChangeNormedSpaceRestrictScalars :
    letI := baseChangeNormedAddCommGroup K V L
    NormedSpace K (V ⊗[K] L) := by
  letI := baseChangeNormedAddCommGroup K V L
  exact { toModule := inferInstance
          norm_smul_le := fun a u =>
            (map_smul_eq_mul (baseChangeSeminorm K V L) a u).le }

end ExtensionScalars

end AlternatingAnalytic
