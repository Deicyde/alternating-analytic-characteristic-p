import AlternatingAnalytic.Analysis.DeterminantCoefficientObstruction
import AlternatingAnalytic.Analysis.DenseScalarFamilyExtension

/-!
# Multilinear obstruction for the determinant coefficient space

The extension takes values only in the complete ambient Laurent field. Its values
on the original source tuples agree with the given coefficient-valued map.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators NNReal

namespace AlternatingAnalytic.DeterminantPair

variable (p : ℕ) [Fact p.Prime] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)]
attribute [local instance] preferredNormedFieldK preferredFieldK preferredFieldL

/-- Extend a coefficient-valued multilinear map only after including its target in `L`. -/
def coefficientMultilinearExtension
    (B : ContinuousMultilinearMap (K p r) (fun _ : Fin p => E p r) (C p r)) :
    ContinuousMultilinearMap (L p r) (fun _ : Fin p => A p r) (L p r) :=
  denseScalarFamilyExtension (RationalField.denseRange_algebraMap (ZMod p) r)
    (fun _ => (E p r).subtypeₗᵢ)
    (fun _ => RigidDenseSource.Concrete.denseRange_subtype p r)
    ((C p r).subtypeL.compContinuousMultilinearMap B)

@[simp] theorem coefficientMultilinearExtension_apply
    (B : ContinuousMultilinearMap (K p r) (fun _ : Fin p => E p r) (C p r))
    (x : Fin p → E p r) :
    coefficientMultilinearExtension p r B (fun i => (x i : A p r)) =
      (B x : L p r) :=
  denseScalarFamilyExtension_apply _ _ _ _ x

/-- Linear expansion in any one original slot gives the actual small-target relation. -/
theorem multilinear_coefficient_relation
    (B : ContinuousMultilinearMap (K p r) (fun _ : Fin p => E p r) (C p r))
    (j : Fin p) (x : Fin p → E p r) :
    (∑ i : Fin p, z p r (Sum.inl i) *
      (B (Function.update x j (RigidDenseSource.Concrete.standard p r i)) : L p r)) ∈
      C p r := by
  let Q := coefficientMultilinearExtension p r B
  have hQ (y : Fin p → E p r) : Q (fun i => (y i : A p r)) = (B y : L p r) :=
    coefficientMultilinearExtension_apply p r B y
  have hupd (y : E p r) :
      (fun i => ((Function.update x j y) i : A p r)) =
        Function.update (fun i => (x i : A p r)) j (y : A p r) := by
    ext i
    by_cases h : i = j <;> simp [h]
  have hstd (i : Fin p) : (RigidDenseSource.Concrete.standard p r i : A p r) = e p r i := by
    rw [RigidDenseSource.Concrete.coe_standard, e_eq_epsilon_pow]
  have heq : Q (Function.update (fun i => (x i : A p r)) j (a p r)) =
      ∑ i : Fin p, z p r (Sum.inl i) *
        (B (Function.update x j (RigidDenseSource.Concrete.standard p r i)) : L p r) := by
    rw [a_expansion]
    change Q.toMultilinearMap _ = _
    rw [Q.toMultilinearMap.map_update_sum]
    apply Finset.sum_congr rfl
    intro i _
    change Q _ = _
    rw [Q.map_update_smul]
    rw [← hstd, ← hupd, hQ]
    rfl
  rw [← heq, ← hupd ⟨a p r, a_mem_E p r⟩, hQ]
  exact (B (Function.update x j ⟨a p r, a_mem_E p r⟩)).property

/-- No continuous coefficient-valued multilinear map has normalized value on the constant tuple. -/
theorem no_multilinear_coordinate :
    ¬ ∃ B : ContinuousMultilinearMap (K p r) (fun _ : Fin p => E p r) (C p r),
      ((B (fun _ => RigidDenseSource.Concrete.standard p r 0)) : L p r) = 1 := by
  rintro ⟨B, hB⟩
  let j : Fin p := ⟨p - 1, by have := (Fact.out : p.Prime).pos; omega⟩
  let x : Fin p → E p r := fun _ => RigidDenseSource.Concrete.standard p r 0
  let b : Fin p → C p r := fun i =>
    B (Function.update x j (RigidDenseSource.Concrete.standard p r i))
  apply no_scalar_coefficient_family p r
  refine ⟨b, ?_, multilinear_coefficient_relation p r B j x⟩
  simpa [b, x, Function.update_eq_self] using hB

end AlternatingAnalytic.DeterminantPair
