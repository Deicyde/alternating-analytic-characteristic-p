import AlternatingAnalytic.Analysis.PaddedCompletions
import AlternatingAnalytic.Analysis.PaddedCrossAction
import AlternatingAnalytic.Analysis.FiniteDimensionalPositive
import AlternatingAnalytic.Analysis.AlternatingActionRegularity

/-!
# Analyticity and the coordinate lift on the concrete completed models

The models `H = A × Lⁿ` and `L` are the actual completions constructed in
`PaddedCompletions`. The conclusions here use their explicit Laurent-field
scalar structures. The coordinate lift is L-valued.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped BigOperators NNReal

namespace AlternatingAnalytic.DeterminantPair.Padding

variable (p : ℕ) [Fact p.Prime] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] (n : ℕ)
attribute [local instance] preferredNormedFieldK preferredFieldK preferredFieldL

local instance completedScalarContinuousMul : ContinuousMul (L p r) :=
  NonUnitalSeminormedRing.toContinuousMul

/-- The actual completed pair action is analytic everywhere over complete L. -/
theorem analyticAt_completedAction
    (h : (H p r n →L[L p r] H p r n) × (L p r →L[L p r] L p r)) :
    AnalyticAt (L p r)
      (alternatingMapAction (K := L p r) (E := H p r n) (E' := H p r n)
        (F := L p r) (F' := L p r) (p+n)) h := by
  apply analyticAt_alternatingMapAction_of_precomposition
  exact analyticAt_Q_of_finiteDimensionalDomain (p+n) h.1

/-- Bounded projection onto the constant coefficient of the algebra component. -/
def constantCoefficient : H p r n →L[L p r] L p r :=
  (ContinuousLinearMap.proj (0 : Fin p)).comp
    ((TruncatedPolynomial.coefficientIsometry (L p r) p).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (ContinuousLinearMap.fst (L p r) (A p r) (Fin n → L p r)))

@[simp] theorem constantCoefficient_apply (z : H p r n) :
    constantCoefficient p r n z = TruncatedPolynomial.coeff (L p r) p z.1 0 := rfl

/-- The literal continuous p-multilinear coordinate product. -/
def coordinateLift : ContinuousMultilinearMap (L p r) (fun _ : Fin p => H p r n) (L p r) :=
  (ContinuousMultilinearMap.mkPiAlgebra (L p r) (Fin p) (L p r)).compContinuousLinearMap
    (fun _ => constantCoefficient p r n)

@[simp] theorem coordinateLift_apply (z : Fin p → H p r n) :
    coordinateLift p r n z = ∏ j, constantCoefficient p r n (z j) := rfl

/-- Its diagonal is exactly the ambient scalar coordinate polynomial. -/
@[simp] theorem coordinateLift_diagonal (z : H p r n) :
    coordinateLift p r n (fun _ => z) = (constantCoefficient p r n z) ^ p := by
  simp [coordinateLift_apply]

/-- On the embedded old source, the diagonal agrees with f after C ↪ L. -/
theorem coordinateLift_original (x : DeterminantPair.E p r) :
    coordinateLift p r n (fun _ => inclusionE p r n (x, 0)) =
      (determinantCoordinate p r x : L p r) := by
  rw [coordinateLift_diagonal, determinantCoordinate_scalar]
  rfl

/-- The completed affine family is literal multiplication on A and identity on Lⁿ. -/
def completedPaddedMultiplication (x : A p r) : H p r n →L[L p r] H p r n :=
  (completedMultiplication p r x).prodMap (ContinuousLinearMap.id (L p r) (Fin n → L p r))

@[simp] theorem completedPaddedMultiplication_apply (x : A p r) (z : H p r n) :
    completedPaddedMultiplication p r n x z = (x * z.1, z.2) := rfl

/-- This L-linear operator extends the specific old K-linear padded operator. -/
theorem completedPaddedMultiplication_original (x : DeterminantPair.E p r) (y : E p r n) :
    completedPaddedMultiplication p r n (x : A p r) (inclusionE p r n y) =
      inclusionD p r n (paddedMultiplication p r n x y) := rfl

/-- The completed multiplication matrix has the actual lower-triangular
multiplication block and the auxiliary identity, including n = 0. -/
theorem completedPaddedMultiplication_matrix (x : A p r) :
    Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm
      (LinearMap.toMatrix (basis p r n) (basis p r n)
        (completedPaddedMultiplication p r n x).toLinearMap) =
      Matrix.fromBlocks (multiplicationMatrix p r x) 0 0
        (1 : Matrix (Fin n) (Fin n) (L p r)) := by
  classical
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.reindex_apply, LinearMap.toMatrix_apply,
      completedPaddedMultiplication_apply, Matrix.fromBlocks,
      multiplicationMatrix, Matrix.one_apply, Pi.single_apply]

/-- The determinant of completed `M_x ⊕ id` is the same constant-coordinate pth power. -/
theorem det_completedPaddedMultiplication (x : A p r) :
    LinearMap.det (completedPaddedMultiplication p r n x).toLinearMap =
      TruncatedPolynomial.coeff (L p r) p x 0 ^ p := by
  classical
  rw [← LinearMap.det_toMatrix (basis p r n),
    ← Matrix.det_reindex_self finSumFinEquiv.symm,
    completedPaddedMultiplication_matrix, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, mul_one, det_multiplicationMatrix]

/-- The normalized ambient determinant as an actual continuous L-alternating map. -/
def completedDeterminant : H p r n [⋀^Fin (p+n)]→L[L p r] L p r :=
  (basis p r n).det.mkContinuous 1 (fun z => by
    change ‖delta p r n z‖ ≤ 1 * ∏ i, ‖z i‖
    rw [one_mul]
    exact norm_delta_le p r n z)

@[simp] theorem completedDeterminant_apply (z : Fin (p+n) → H p r n) :
    completedDeterminant p r n z = delta p r n z := rfl

/-- The completed L-valued determinant extends the original G-valued determinant. -/
theorem completedDeterminant_original (z : Fin (p+n) → D p r n) :
    completedDeterminant p r n (fun i => inclusionD p r n (z i)) =
      (determinantD p r n z : L p r) := rfl

/-- The diagonal lift is the exact completed determinant slice. -/
theorem coordinateLift_completedDeterminant (z : H p r n) :
    coordinateLift p r n (fun _ => z) =
      delta p r n (fun i => completedPaddedMultiplication p r n z.1 (basis p r n i)) := by
  rw [coordinateLift_diagonal, constantCoefficient_apply]
  change _ = (basis p r n).det
    ((completedPaddedMultiplication p r n z.1).toLinearMap ∘ basis p r n)
  rw [Module.Basis.det_comp, det_completedPaddedMultiplication, Module.Basis.det_self, mul_one]

/-- The exact action/evaluation slice on the completed pair is this coordinate lift. -/
theorem coordinateLift_completedAction (z : H p r n) :
    coordinateLift p r n (fun _ => z) =
      alternatingMapAction (p+n)
        (completedPaddedMultiplication p r n z.1, ContinuousLinearMap.id (L p r) (L p r))
        (completedDeterminant p r n) (basis p r n) :=
  coordinateLift_completedDeterminant p r n z

/-- It also agrees with the original C-valued obstruction observation, in L. -/
theorem coordinateLift_originalAction (x : DeterminantPair.E p r) :
    coordinateLift p r n (fun _ => inclusionE p r n (x, 0)) =
      (crossActionEvaluation p r n
        (alternatingMapAction (p+n) (crossActionSlice p r n x)) : L p r) := by
  rw [crossActionEvaluation_slice, coordinateLift_original]

/-- The scalar-extension conclusion of `dom:limits` for these concrete models,
including the literal bounded multilinear lift and the determinant slice. -/
theorem concrete_completed_analytic_action_and_lift :
    CompleteSpace (H p r n) ∧ FiniteDimensional (L p r) (H p r n) ∧
    CompleteSpace (L p r) ∧
    (∀ h : (H p r n →L[L p r] H p r n) × (L p r →L[L p r] L p r),
      AnalyticAt (L p r)
        (alternatingMapAction (K := L p r) (E := H p r n) (E' := H p r n)
          (F := L p r) (F' := L p r) (p+n)) h) ∧
    (∀ z : Fin p → H p r n,
      coordinateLift p r n z = ∏ j, constantCoefficient p r n (z j)) ∧
    (∀ z : H p r n,
      coordinateLift p r n (fun _ => z) = (constantCoefficient p r n z) ^ p) ∧
    (∀ x : DeterminantPair.E p r,
      coordinateLift p r n (fun _ => inclusionE p r n (x, 0)) =
        (determinantCoordinate p r x : L p r)) ∧
    (∀ (x : DeterminantPair.E p r) (y : E p r n),
      completedPaddedMultiplication p r n (x : A p r) (inclusionE p r n y) =
        inclusionD p r n (paddedMultiplication p r n x y)) ∧
    (∀ z : H p r n,
      coordinateLift p r n (fun _ => z) =
        delta p r n (fun i => completedPaddedMultiplication p r n z.1 (basis p r n i))) ∧
    (∀ x : A p r,
      LinearMap.det (completedPaddedMultiplication p r n x).toLinearMap =
        TruncatedPolynomial.coeff (L p r) p x 0 ^ p) ∧
    (∀ z : Fin (p+n) → D p r n,
      completedDeterminant p r n (fun i => inclusionD p r n (z i)) =
        (determinantD p r n z : L p r)) ∧
    (∀ z : H p r n,
      coordinateLift p r n (fun _ => z) =
        alternatingMapAction (p+n)
          (completedPaddedMultiplication p r n z.1, ContinuousLinearMap.id (L p r) (L p r))
          (completedDeterminant p r n) (basis p r n)) ∧
    (∀ x : DeterminantPair.E p r,
      coordinateLift p r n (fun _ => inclusionE p r n (x, 0)) =
        (crossActionEvaluation p r n
          (alternatingMapAction (p+n) (crossActionSlice p r n x)) : L p r)) := by
  exact ⟨inferInstance, inferInstance, inferInstance, analyticAt_completedAction p r n,
    coordinateLift_apply p r n, coordinateLift_diagonal p r n,
    coordinateLift_original p r n, completedPaddedMultiplication_original p r n,
    coordinateLift_completedDeterminant p r n, det_completedPaddedMultiplication p r n,
    completedDeterminant_original p r n, coordinateLift_completedAction p r n,
    coordinateLift_originalAction p r n⟩

end AlternatingAnalytic.DeterminantPair.Padding
