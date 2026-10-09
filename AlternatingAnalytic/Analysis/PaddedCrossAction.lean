import AlternatingAnalytic.Analysis.DeterminantCrossActionObstruction
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# The cross-action between the padded pairs

Along the bounded affine family `x ↦ M_x ⊕ id` from `E` to `L(E_k, D_k)`, evaluating the action at
`det_k` and taking the coefficient in `C` gives the nonanalytic coordinate of Appendix H. Hence the
cross-action from `(D_k, G)` to `(E_k, G)` is not analytic (proof of Theorem H.4).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators NNReal

namespace AlternatingAnalytic.DeterminantPair.Padding

variable (p : ℕ) [Fact p.Prime] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] (n : ℕ)
attribute [local instance] preferredNormedFieldK preferredFieldK preferredFieldL

/-- The linear part `x ↦ M_x ⊕ 0`. -/
def multiplicationLinearPart :
    DeterminantPair.E p r →L[K p r] E p r n →L[K p r] D p r n :=
  (ContinuousLinearMap.prodMapL (K p r) (DeterminantPair.E p r)
    (DeterminantPair.D p r) (Fin n → K p r) (Fin n → K p r)).comp
      ((DeterminantPair.multiplication p r).prod 0)

/-- The constant part `0 ⊕ id`; `n = 0` is allowed. -/
def auxiliaryIdentity : E p r n →L[K p r] D p r n :=
  (0 : DeterminantPair.E p r →L[K p r] DeterminantPair.D p r).prodMap
    (ContinuousLinearMap.id (K p r) (Fin n → K p r))

/-- The bounded affine family `M_x ⊕ id : E_k → D_k`. -/
def paddedMultiplication (x : DeterminantPair.E p r) : E p r n →L[K p r] D p r n :=
  (DeterminantPair.multiplication p r x).prodMap
    (ContinuousLinearMap.id (K p r) (Fin n → K p r))

@[simp] theorem paddedMultiplication_apply (x : DeterminantPair.E p r) (y : E p r n) :
    paddedMultiplication p r n x y = (DeterminantPair.multiplication p r x y.1, y.2) := rfl

theorem paddedMultiplication_eq_affine (x : DeterminantPair.E p r) :
    paddedMultiplication p r n x = multiplicationLinearPart p r n x + auxiliaryIdentity p r n := by
  ext y <;> simp [paddedMultiplication, multiplicationLinearPart, auxiliaryIdentity]

@[simp] theorem paddedMultiplication_zero :
    paddedMultiplication p r n 0 = auxiliaryIdentity p r n := by
  rw [paddedMultiplication_eq_affine, map_zero, zero_add]

theorem analyticAt_paddedMultiplication (x : DeterminantPair.E p r) :
    AnalyticAt (K p r) (paddedMultiplication p r n) x := by
  change AnalyticAt (K p r) (fun y => paddedMultiplication p r n y) x
  simp_rw [paddedMultiplication_eq_affine]
  exact ((multiplicationLinearPart p r n).analyticAt x).add analyticAt_const

/-- `M_x ⊕ id` sends the standard tuple of `E_k` to the multiplication tuple followed by the
auxiliary basis. -/
theorem paddedMultiplication_standard (x : DeterminantPair.E p r) :
    (fun i => paddedMultiplication p r n x (standardE p r n i)) =
      padTuple p r n (DeterminantPair.D p r)
        (fun i => DeterminantPair.multiplication p r x
          (RigidDenseSource.Concrete.standard p r i)) := by
  funext i
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  cases i with
  | inl i => simp [standardE, padTuple, paddedMultiplication_apply]
  | inr i => simp [standardE, padTuple, paddedMultiplication_apply]

/-- The coefficient of `det_k ∘ (M_x ⊕ id)` is the determinant coordinate of `x`. -/
theorem paddedCoefficient_multiplication (x : DeterminantPair.E p r) :
    paddedCoefficientEquiv p r n
      ((determinantD p r n).compContinuousLinearMap (paddedMultiplication p r n x)) =
      determinantCoordinate p r x := by
  apply Subtype.ext
  change (determinantD p r n (fun i => paddedMultiplication p r n x
    (standardE p r n i)) : L p r) = _
  rw [paddedMultiplication_standard, determinantD_apply]
  change delta p r n (fun i =>
    ((padTuple p r n (DeterminantPair.D p r)
      (fun j => DeterminantPair.multiplication p r x
        (RigidDenseSource.Concrete.standard p r j)) i).1,
      fun j => algebraMap (K p r) (L p r)
        ((padTuple p r n (DeterminantPair.D p r)
          (fun j => DeterminantPair.multiplication p r x
            (RigidDenseSource.Concrete.standard p r j)) i).2 j))) = _
  rw [delta_padTuple]
  rw [← DeterminantPair.determinantD_apply]
  rfl

/-- Evaluation at `det_k` followed by the coefficient isometry onto `C`. -/
def crossActionEvaluation :
    ((D p r n [⋀^Fin (p+n)]→L[K p r] G p r) →L[K p r]
      (E p r n [⋀^Fin (p+n)]→L[K p r] G p r)) →L[K p r] C p r :=
  (paddedCoefficientEquiv p r n).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (ContinuousLinearMap.apply (K p r) (E p r n [⋀^Fin (p+n)]→L[K p r] G p r)
      (determinantD p r n))

/-- The slice `x ↦ (M_x ⊕ id, id_G)` of the joint action. -/
def crossActionSlice (x : DeterminantPair.E p r) :
    (E p r n →L[K p r] D p r n) × (G p r →L[K p r] G p r) :=
  (paddedMultiplication p r n x, ContinuousLinearMap.id (K p r) (G p r))

@[simp] theorem crossActionSlice_zero :
    crossActionSlice p r n 0 =
      (auxiliaryIdentity p r n, ContinuousLinearMap.id (K p r) (G p r)) := by
  simp [crossActionSlice]

theorem analyticAt_crossActionSlice (x : DeterminantPair.E p r) :
    AnalyticAt (K p r) (crossActionSlice p r n) x :=
  (analyticAt_paddedMultiplication p r n x).prod analyticAt_const

/-- Along the slice, evaluation gives the determinant coordinate. -/
theorem crossActionEvaluation_slice (x : DeterminantPair.E p r) :
    crossActionEvaluation p r n
      (alternatingMapAction (p+n) (crossActionSlice p r n x)) = determinantCoordinate p r x := by
  change paddedCoefficientEquiv p r n _ = _
  rw [← paddedCoefficient_multiplication p r n x]
  congr 1

/-- The joint cross-action is not analytic at `(0 ⊕ id, id_G)`. -/
theorem not_analyticAt_crossAction :
    ¬ AnalyticAt (K p r)
      (alternatingMapAction (K := K p r) (E := D p r n) (E' := E p r n)
        (F := G p r) (F' := G p r) (p+n))
      (auxiliaryIdentity p r n, ContinuousLinearMap.id (K p r) (G p r)) := by
  intro h
  apply not_analyticAt_determinantCoordinate p r
  have hs := h.comp_of_eq (analyticAt_crossActionSlice p r n 0) (crossActionSlice_zero p r n)
  have he := ((crossActionEvaluation p r n).analyticAt _).comp hs
  simpa only [Function.comp_def, crossActionEvaluation_slice] using he

/-- Summary: the affine family, the evaluation formula, and nonanalyticity of the
cross-action. -/
theorem padded_nonanalytic_cross_action :
    (∀ x : DeterminantPair.E p r,
      paddedMultiplication p r n x = multiplicationLinearPart p r n x + auxiliaryIdentity p r n) ∧
    (∀ (x : DeterminantPair.E p r) (y : E p r n),
      paddedMultiplication p r n x y = (DeterminantPair.multiplication p r x y.1, y.2)) ∧
    (∀ x : DeterminantPair.E p r, AnalyticAt (K p r) (crossActionSlice p r n) x) ∧
    (∀ x : DeterminantPair.E p r,
      crossActionEvaluation p r n (alternatingMapAction (p+n) (crossActionSlice p r n x)) =
        determinantCoordinate p r x) ∧
    (∀ x : DeterminantPair.E p r,
      (crossActionEvaluation p r n
        (alternatingMapAction (p+n) (crossActionSlice p r n x)) : L p r) =
          TruncatedPolynomial.coeff (L p r) p (x : A p r) 0 ^ p) ∧
    crossActionSlice p r n 0 =
      (auxiliaryIdentity p r n, ContinuousLinearMap.id (K p r) (G p r)) ∧
    ¬ AnalyticAt (K p r)
      (alternatingMapAction (K := K p r) (E := D p r n) (E' := E p r n)
        (F := G p r) (F' := G p r) (p+n))
      (auxiliaryIdentity p r n, ContinuousLinearMap.id (K p r) (G p r)) := by
  refine ⟨paddedMultiplication_eq_affine p r n, paddedMultiplication_apply p r n,
    analyticAt_crossActionSlice p r n, crossActionEvaluation_slice p r n,
    ?_, crossActionSlice_zero p r n, not_analyticAt_crossAction p r n⟩
  intro x
  rw [crossActionEvaluation_slice, determinantCoordinate_scalar]

end AlternatingAnalytic.DeterminantPair.Padding
