/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
import AlternatingAnalytic.Analysis.CompletedProjectiveTensor

/-!
# Homogeneous tensor reflection

The closed span of diagonal powers in the ordinary completed projective tensor power is
complemented precisely when every continuous multilinear diagonal in a closed subspace
has a continuous multilinear representative in that subspace. A supplied retraction gives
an explicit representative of norm at most the original norm times the retraction norm.

This formalizes `fam:prop:tensor-homogeneous`. The components also allow degree zero.
-/

namespace AlternatingAnalytic

universe u v

variable {K P : Type u} [NontriviallyNormedField K]
  [NormedAddCommGroup P] [NormedSpace K P]

/-- The ordinary separated completed projective tensor power. -/
abbrev TensorPower (K P : Type u) [NontriviallyNormedField K]
    [NormedAddCommGroup P] [NormedSpace K P] (n : ℕ) :=
  CompletedProjectiveTensor K (fun _ : Fin n => P)

/-- A diagonal pure tensor; this map is generally polynomial rather than linear. -/
noncomputable def diagonalTensor (n : ℕ) (x : P) : TensorPower K P n :=
  completedProjectiveTensorTprod (K := K) (fun _ : Fin n => P) (fun _ => x)

/-- The closed linear span of the diagonal pure tensors. -/
noncomputable def DiagonalSpan (K P : Type u) [NontriviallyNormedField K]
    [NormedAddCommGroup P] [NormedSpace K P] (n : ℕ) : Submodule K (TensorPower K P n) :=
  (Submodule.span K (Set.range (diagonalTensor (K := K) (P := P) n))).topologicalClosure

theorem diagonalTensor_mem (n : ℕ) (x : P) :
    diagonalTensor (K := K) n x ∈ DiagonalSpan K P n :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨x, rfl⟩)

theorem isClosed_diagonalSpan (n : ℕ) :
    IsClosed (DiagonalSpan K P n : Set (TensorPower K P n)) :=
  Submodule.isClosed_topologicalClosure _

instance (n : ℕ) : CompleteSpace (DiagonalSpan K P n) :=
  (isClosed_diagonalSpan (K := K) (P := P) n).completeSpace_coe

variable {n : ℕ} {Z : Type v}
  [NormedAddCommGroup Z] [NormedSpace K Z] [CompleteSpace Z]

/-- Closedness of the inverse image extends diagonal membership to the closed span. -/
theorem linearized_mem_of_mem_diagonalSpan
    (W : Submodule K Z) (hW : IsClosed (W : Set Z))
    (B : ContinuousMultilinearMap K (fun _ : Fin n => P) Z)
    (hB : ∀ x, B (fun _ => x) ∈ W)
    {t : TensorPower K P n} (ht : t ∈ DiagonalSpan K P n) :
    completedProjectiveTensorLiftIsometry (fun _ : Fin n => P) Z B t ∈ W := by
  let L := completedProjectiveTensorLiftIsometry (fun _ : Fin n => P) Z B
  have hspan : Submodule.span K (Set.range (diagonalTensor (K := K) (P := P) n)) ≤
      W.comap L.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    change L (diagonalTensor n x) ∈ W
    simpa only [L, diagonalTensor, completedProjectiveTensorLiftIsometry_tprod] using hB x
  have hclosed : IsClosed (W.comap L.toLinearMap : Set (TensorPower K P n)) :=
    hW.preimage L.continuous
  exact Submodule.topologicalClosure_minimal _ hspan hclosed ht

/-- The actual linearization restricted to the diagonal span and to the closed target. -/
noncomputable def diagonalSpanLift
    (W : Submodule K Z) (hW : IsClosed (W : Set Z))
    (B : ContinuousMultilinearMap K (fun _ : Fin n => P) Z)
    (hB : ∀ x, B (fun _ => x) ∈ W) : DiagonalSpan K P n →L[K] W :=
  (completedProjectiveTensorLiftIsometry (fun _ : Fin n => P) Z B).restrict
    (fun _ ht => linearized_mem_of_mem_diagonalSpan W hW B hB ht)

@[simp]
theorem diagonalSpanLift_apply
    (W : Submodule K Z) (hW : IsClosed (W : Set Z))
    (B : ContinuousMultilinearMap K (fun _ : Fin n => P) Z)
    (hB : ∀ x, B (fun _ => x) ∈ W) (t : DiagonalSpan K P n) :
    (diagonalSpanLift W hW B hB t : Z) =
      completedProjectiveTensorLiftIsometry (fun _ : Fin n => P) Z B t := rfl

theorem norm_diagonalSpanLift_le
    (W : Submodule K Z) (hW : IsClosed (W : Set Z))
    (B : ContinuousMultilinearMap K (fun _ : Fin n => P) Z)
    (hB : ∀ x, B (fun _ => x) ∈ W) :
    ‖diagonalSpanLift W hW B hB‖ ≤ ‖B‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B)
  intro t
  change ‖completedProjectiveTensorLiftIsometry (fun _ : Fin n => P) Z B t‖ ≤ ‖B‖ * ‖t‖
  simpa only [norm_completedProjectiveTensorLiftIsometry, Submodule.norm_coe] using
    (completedProjectiveTensorLiftIsometry (fun _ : Fin n => P) Z B).le_opNorm t

/-- Compose the restricted linearization, the supplied retraction, and the canonical map. -/
noncomputable def diagonalLiftOfProjection
    (R : TensorPower K P n →L[K] DiagonalSpan K P n)
    (W : Submodule K Z) (hW : IsClosed (W : Set Z))
    (B : ContinuousMultilinearMap K (fun _ : Fin n => P) Z)
    (hB : ∀ x, B (fun _ => x) ∈ W) :
    ContinuousMultilinearMap K (fun _ : Fin n => P) W :=
  ((diagonalSpanLift W hW B hB).comp R).compContinuousMultilinearMap
    (completedProjectiveTensorTprod (fun _ : Fin n => P))

theorem diagonalLiftOfProjection_diag
    (R : TensorPower K P n →L[K] DiagonalSpan K P n)
    (hR : R.comp (DiagonalSpan K P n).subtypeL =
      ContinuousLinearMap.id K (DiagonalSpan K P n))
    (W : Submodule K Z) (hW : IsClosed (W : Set Z))
    (B : ContinuousMultilinearMap K (fun _ : Fin n => P) Z)
    (hB : ∀ x, B (fun _ => x) ∈ W) (x : P) :
    (diagonalLiftOfProjection R W hW B hB (fun _ => x) : Z) = B (fun _ => x) := by
  have hfix : R (diagonalTensor (K := K) n x) =
      ⟨diagonalTensor (K := K) n x, diagonalTensor_mem n x⟩ :=
    DFunLike.congr_fun hR ⟨diagonalTensor (K := K) n x, diagonalTensor_mem n x⟩
  change (diagonalSpanLift W hW B hB (R (diagonalTensor n x)) : Z) = _
  rw [hfix, diagonalSpanLift_apply]
  exact completedProjectiveTensorLiftIsometry_tprod _ B _

theorem norm_diagonalLiftOfProjection_le
    (R : TensorPower K P n →L[K] DiagonalSpan K P n)
    (W : Submodule K Z) (hW : IsClosed (W : Set Z))
    (B : ContinuousMultilinearMap K (fun _ : Fin n => P) Z)
    (hB : ∀ x, B (fun _ => x) ∈ W) :
    ‖diagonalLiftOfProjection R W hW B hB‖ ≤ ‖B‖ * ‖R‖ := by
  calc
    ‖diagonalLiftOfProjection R W hW B hB‖ ≤
        ‖(diagonalSpanLift W hW B hB).comp R‖ *
          ‖completedProjectiveTensorTprod (K := K) (fun _ : Fin n => P)‖ :=
      ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ ≤ ‖(diagonalSpanLift W hW B hB).comp R‖ * 1 :=
      mul_le_mul_of_nonneg_left (norm_completedProjectiveTensorTprod_le _) (norm_nonneg _)
    _ = ‖(diagonalSpanLift W hW B hB).comp R‖ := mul_one _
    _ ≤ ‖diagonalSpanLift W hW B hB‖ * ‖R‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖B‖ * ‖R‖ :=
      mul_le_mul_of_nonneg_right (norm_diagonalSpanLift_le W hW B hB) (norm_nonneg R)

/-- A map into the diagonal span that fixes its generators is a retraction on that span. -/
theorem retraction_of_fixes_diagonalTensor
    (R : TensorPower K P n →L[K] DiagonalSpan K P n)
    (hR : ∀ x, (R (diagonalTensor (K := K) n x) : TensorPower K P n) =
      diagonalTensor (K := K) n x) :
    R.comp (DiagonalSpan K P n).subtypeL =
      ContinuousLinearMap.id K (DiagonalSpan K P n) := by
  have hgen : Set.EqOn ((DiagonalSpan K P n).subtypeL.comp R)
      (ContinuousLinearMap.id K (TensorPower K P n))
      (Set.range (diagonalTensor (K := K) (P := P) n)) := by
    rintro _ ⟨x, rfl⟩
    exact hR x
  have hspan := ContinuousLinearMap.eqOn_closure_span hgen
  apply ContinuousLinearMap.ext
  intro t
  apply Subtype.ext
  exact hspan t.property

section Source

/-- A supplied projection gives one representative with both the correct diagonal and
the stated norm bound, in any target universe. -/
theorem exists_diagonal_lift_of_projection [CompleteSpace K] [CompleteSpace P]
    (n : ℕ) (R : TensorPower K P n →L[K] DiagonalSpan K P n)
    (hR : R.comp (DiagonalSpan K P n).subtypeL =
      ContinuousLinearMap.id K (DiagonalSpan K P n))
    (W : Submodule K Z) (hW : IsClosed (W : Set Z))
    (B : ContinuousMultilinearMap K (fun _ : Fin n => P) Z)
    (hB : ∀ x, B (fun _ => x) ∈ W) :
    ∃ C : ContinuousMultilinearMap K (fun _ : Fin n => P) W,
      (∀ x, (C (fun _ => x) : Z) = B (fun _ => x)) ∧ ‖C‖ ≤ ‖B‖ * ‖R‖ := by
  exact ⟨diagonalLiftOfProjection R W hW B hB,
    diagonalLiftOfProjection_diag R hR W hW B hB,
    norm_diagonalLiftOfProjection_le R W hW B hB⟩

variable [CompleteSpace K] [CompleteSpace P]

/-- Universal diagonal lifting is equivalent to a bounded retraction onto the actual
closed diagonal span. The target universe includes the completed tensor power itself. -/
theorem homogeneous_reflection_iff_projection (n : ℕ) :
    (∀ (Z : Type u) [NormedAddCommGroup Z] [NormedSpace K Z] [CompleteSpace Z],
      ∀ (W : Submodule K Z), IsClosed (W : Set Z) →
      ∀ B : ContinuousMultilinearMap K (fun _ : Fin n => P) Z,
        (∀ x, B (fun _ => x) ∈ W) →
        ∃ C : ContinuousMultilinearMap K (fun _ : Fin n => P) W,
          ∀ x, (C (fun _ => x) : Z) = B (fun _ => x)) ↔
    ∃ R : TensorPower K P n →L[K] DiagonalSpan K P n,
      R.comp (DiagonalSpan K P n).subtypeL =
        ContinuousLinearMap.id K (DiagonalSpan K P n) := by
  constructor
  · intro h
    obtain ⟨C, hC⟩ := h (TensorPower K P n) (DiagonalSpan K P n)
      (isClosed_diagonalSpan n) (completedProjectiveTensorTprod (fun _ : Fin n => P))
      (diagonalTensor_mem n)
    refine ⟨completedProjectiveTensorLiftIsometry (fun _ : Fin n => P)
      (DiagonalSpan K P n) C, retraction_of_fixes_diagonalTensor _ ?_⟩
    intro x
    simpa only [diagonalTensor, completedProjectiveTensorLiftIsometry_tprod] using hC x
  · rintro ⟨R, hR⟩ Z _ _ _ W hW B hB
    obtain ⟨C, hC, _⟩ := exists_diagonal_lift_of_projection n R hR W hW B hB
    exact ⟨C, hC⟩

/-- Homogeneous tensor reflection, including its quantitative construction: every supplied
projection produces a single multilinear lift with the exact diagonal and norm bound.
The all-natural-degree formulation extends the source's positive-degree statement. -/
theorem homogeneous_tensor_reflection (n : ℕ) :
    ((∀ (Z : Type u) [NormedAddCommGroup Z] [NormedSpace K Z] [CompleteSpace Z],
      ∀ (W : Submodule K Z), IsClosed (W : Set Z) →
      ∀ B : ContinuousMultilinearMap K (fun _ : Fin n => P) Z,
        (∀ x, B (fun _ => x) ∈ W) →
        ∃ C : ContinuousMultilinearMap K (fun _ : Fin n => P) W,
          ∀ x, (C (fun _ => x) : Z) = B (fun _ => x)) ↔
      ∃ R : TensorPower K P n →L[K] DiagonalSpan K P n,
        R.comp (DiagonalSpan K P n).subtypeL =
          ContinuousLinearMap.id K (DiagonalSpan K P n)) ∧
    (∀ (R : TensorPower K P n →L[K] DiagonalSpan K P n),
      R.comp (DiagonalSpan K P n).subtypeL =
        ContinuousLinearMap.id K (DiagonalSpan K P n) →
      ∀ (Z : Type v) [NormedAddCommGroup Z] [NormedSpace K Z] [CompleteSpace Z],
      ∀ (W : Submodule K Z), IsClosed (W : Set Z) →
      ∀ B : ContinuousMultilinearMap K (fun _ : Fin n => P) Z,
        (∀ x, B (fun _ => x) ∈ W) →
        ∃ C : ContinuousMultilinearMap K (fun _ : Fin n => P) W,
          (∀ x, (C (fun _ => x) : Z) = B (fun _ => x)) ∧ ‖C‖ ≤ ‖B‖ * ‖R‖) := by
  refine ⟨homogeneous_reflection_iff_projection n, ?_⟩
  intro R hR Z _ _ _ W hW B hB
  exact exists_diagonal_lift_of_projection n R hR W hW B hB

/-- The positive-degree form of `fam:prop:tensor-homogeneous`, with the quantitative
conclusion from its proof included in the same statement. -/
theorem homogeneous_tensor_reflection_of_one_le (n : ℕ) (_hn : 1 ≤ n) :
    ((∀ (Z : Type u) [NormedAddCommGroup Z] [NormedSpace K Z] [CompleteSpace Z],
      ∀ (W : Submodule K Z), IsClosed (W : Set Z) →
      ∀ B : ContinuousMultilinearMap K (fun _ : Fin n => P) Z,
        (∀ x, B (fun _ => x) ∈ W) →
        ∃ C : ContinuousMultilinearMap K (fun _ : Fin n => P) W,
          ∀ x, (C (fun _ => x) : Z) = B (fun _ => x)) ↔
      ∃ R : TensorPower K P n →L[K] DiagonalSpan K P n,
        R.comp (DiagonalSpan K P n).subtypeL =
          ContinuousLinearMap.id K (DiagonalSpan K P n)) ∧
    (∀ (R : TensorPower K P n →L[K] DiagonalSpan K P n),
      R.comp (DiagonalSpan K P n).subtypeL =
        ContinuousLinearMap.id K (DiagonalSpan K P n) →
      ∀ (Z : Type v) [NormedAddCommGroup Z] [NormedSpace K Z] [CompleteSpace Z],
      ∀ (W : Submodule K Z), IsClosed (W : Set Z) →
      ∀ B : ContinuousMultilinearMap K (fun _ : Fin n => P) Z,
        (∀ x, B (fun _ => x) ∈ W) →
        ∃ C : ContinuousMultilinearMap K (fun _ : Fin n => P) W,
          (∀ x, (C (fun _ => x) : Z) = B (fun _ => x)) ∧ ‖C‖ ≤ ‖B‖ * ‖R‖) :=
  homogeneous_tensor_reflection n

end Source

/-- At degree zero every pure tensor is a diagonal tensor, so the diagonal span is full. -/
theorem diagonalSpan_zero : DiagonalSpan K P 0 = ⊤ := by
  have hrange : Set.range (diagonalTensor (K := K) (P := P) 0) =
      Set.range (completedProjectiveTensorTprod (K := K) (fun _ : Fin 0 => P)) := by
    ext t
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨fun _ => x, rfl⟩
    · rintro ⟨x, rfl⟩
      refine ⟨0, ?_⟩
      exact congrArg (completedProjectiveTensorTprod (K := K) (fun _ : Fin 0 => P))
        (Subsingleton.elim _ _)
  rw [DiagonalSpan, hrange]
  exact completedProjectiveTensor_tprod_dense_span (fun _ : Fin 0 => P)

/-- For a trivial parameter space, every positive-degree completed tensor is zero. -/
theorem tensorPower_eq_zero_of_subsingleton [Subsingleton P] (hn : 0 < n)
    (t : TensorPower K P n) : t = 0 := by
  have hrange : Set.range (completedProjectiveTensorTprod (K := K) (fun _ : Fin n => P)) ⊆
      (⊥ : Submodule K (TensorPower K P n)) := by
    rintro _ ⟨x, rfl⟩
    exact (completedProjectiveTensorTprod (K := K) (fun _ : Fin n => P)).map_coord_zero
      ⟨0, hn⟩ (Subsingleton.elim _ _)
  have hclosure := Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr hrange)
    (show IsClosed ((⊥ : Submodule K (TensorPower K P n)) : Set (TensorPower K P n)) by
      simp)
  rw [completedProjectiveTensor_tprod_dense_span] at hclosure
  exact hclosure (Submodule.mem_top : t ∈ (⊤ : Submodule K (TensorPower K P n)))

end AlternatingAnalytic
