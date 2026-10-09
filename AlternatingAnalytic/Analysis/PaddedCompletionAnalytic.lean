import AlternatingAnalytic.Analysis.PaddedCompletions
import AlternatingAnalytic.Analysis.PaddedCrossAction
import AlternatingAnalytic.Analysis.FiniteDimensionalPositive
import AlternatingAnalytic.Analysis.AlternatingActionRegularity

/-!
# The padded pairs after completion

After completion over `L = F_p((t))`, both `E_k` and `D_k` become `H = A × Lⁿ`, a
finite-dimensional space over a complete field. There the joint action is analytic and the bad
coordinate `x ↦ x₀ ^ p` of Appendix H has a bounded `L`-valued `p`-linear lift. This is the
closing remark of Appendix H: completion removes the obstruction of Theorem H.4.
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

/-- The joint action on `(H, L)` is analytic everywhere. -/
theorem analyticAt_completedAction
    (h : (H p r n →L[L p r] H p r n) × (L p r →L[L p r] L p r)) :
    AnalyticAt (L p r)
      (alternatingMapAction (K := L p r) (E := H p r n) (E' := H p r n)
        (F := L p r) (F' := L p r) (p+n)) h := by
  apply analyticAt_alternatingMapAction_of_precomposition
  exact analyticAt_Q_of_finiteDimensionalDomain (p+n) h.1

/-- The constant coefficient of the `A` component, as an `L`-linear functional on `H`. -/
def constantCoefficient : H p r n →L[L p r] L p r :=
  (ContinuousLinearMap.proj (0 : Fin p)).comp
    ((TruncatedPolynomial.coefficientIsometry (L p r) p).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (ContinuousLinearMap.fst (L p r) (A p r) (Fin n → L p r)))

@[simp] theorem constantCoefficient_apply (z : H p r n) :
    constantCoefficient p r n z = TruncatedPolynomial.coeff (L p r) p z.1 0 := rfl

/-- The `p`-linear map `(z₁, …, z_p) ↦ ∏ⱼ constantCoefficient zⱼ`. -/
def coordinateLift : ContinuousMultilinearMap (L p r) (fun _ : Fin p => H p r n) (L p r) :=
  (ContinuousMultilinearMap.mkPiAlgebra (L p r) (Fin p) (L p r)).compContinuousLinearMap
    (fun _ => constantCoefficient p r n)

@[simp] theorem coordinateLift_apply (z : Fin p → H p r n) :
    coordinateLift p r n z = ∏ j, constantCoefficient p r n (z j) := rfl

/-- Its diagonal is the `p`-th power of the constant coefficient. -/
@[simp] theorem coordinateLift_diagonal (z : H p r n) :
    coordinateLift p r n (fun _ => z) = (constantCoefficient p r n z) ^ p := by
  simp [coordinateLift_apply]

/-- On `E ⊆ H` the diagonal is the determinant coordinate. -/
theorem coordinateLift_original (x : DeterminantPair.E p r) :
    coordinateLift p r n (fun _ => inclusionE p r n (x, 0)) =
      (determinantCoordinate p r x : L p r) := by
  rw [coordinateLift_diagonal, determinantCoordinate_scalar]
  rfl

/-- Multiplication by `x` on `A` and the identity on `Lⁿ`. -/
def completedPaddedMultiplication (x : A p r) : H p r n →L[L p r] H p r n :=
  (completedMultiplication p r x).prodMap (ContinuousLinearMap.id (L p r) (Fin n → L p r))

@[simp] theorem completedPaddedMultiplication_apply (x : A p r) (z : H p r n) :
    completedPaddedMultiplication p r n x z = (x * z.1, z.2) := rfl

/-- It extends the operator `M_x ⊕ id : E_k → D_k`. -/
theorem completedPaddedMultiplication_original (x : DeterminantPair.E p r) (y : E p r n) :
    completedPaddedMultiplication p r n (x : A p r) (inclusionE p r n y) =
      inclusionD p r n (paddedMultiplication p r n x y) := rfl

/-- In the standard basis, `M_x ⊕ id` has diagonal blocks `multiplicationMatrix x` and `1`. -/
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

/-- `det (M_x ⊕ id) = x₀ ^ p`. -/
theorem det_completedPaddedMultiplication (x : A p r) :
    LinearMap.det (completedPaddedMultiplication p r n x).toLinearMap =
      TruncatedPolynomial.coeff (L p r) p x 0 ^ p := by
  classical
  rw [← LinearMap.det_toMatrix (basis p r n),
    ← Matrix.det_reindex_self finSumFinEquiv.symm,
    completedPaddedMultiplication_matrix, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, mul_one, det_multiplicationMatrix]

/-- The normalized determinant on `H` as a continuous `L`-alternating map. -/
def completedDeterminant : H p r n [⋀^Fin (p+n)]→L[L p r] L p r :=
  (basis p r n).det.mkContinuous 1 (fun z => by
    change ‖delta p r n z‖ ≤ 1 * ∏ i, ‖z i‖
    rw [one_mul]
    exact norm_delta_le p r n z)

@[simp] theorem completedDeterminant_apply (z : Fin (p+n) → H p r n) :
    completedDeterminant p r n z = delta p r n z := rfl

/-- It extends the determinant `det_k` on `D_k`. -/
theorem completedDeterminant_original (z : Fin (p+n) → D p r n) :
    completedDeterminant p r n (fun i => inclusionD p r n (z i)) =
      (determinantD p r n z : L p r) := rfl

/-- The diagonal of the lift is the determinant of `M_x ⊕ id` on the standard basis. -/
theorem coordinateLift_completedDeterminant (z : H p r n) :
    coordinateLift p r n (fun _ => z) =
      delta p r n (fun i => completedPaddedMultiplication p r n z.1 (basis p r n i)) := by
  rw [coordinateLift_diagonal, constantCoefficient_apply]
  change _ = (basis p r n).det
    ((completedPaddedMultiplication p r n z.1).toLinearMap ∘ basis p r n)
  rw [Module.Basis.det_comp, det_completedPaddedMultiplication, Module.Basis.det_self, mul_one]

/-- The diagonal of the lift is the completed action evaluated at the determinant and the
standard basis. -/
theorem coordinateLift_completedAction (z : H p r n) :
    coordinateLift p r n (fun _ => z) =
      alternatingMapAction (p+n)
        (completedPaddedMultiplication p r n z.1, ContinuousLinearMap.id (L p r) (L p r))
        (completedDeterminant p r n) (basis p r n) :=
  coordinateLift_completedDeterminant p r n z

/-- On `E` the diagonal agrees with the cross-action coordinate over `K`. -/
theorem coordinateLift_originalAction (x : DeterminantPair.E p r) :
    coordinateLift p r n (fun _ => inclusionE p r n (x, 0)) =
      (crossActionEvaluation p r n
        (alternatingMapAction (p+n) (crossActionSlice p r n x)) : L p r) := by
  rw [crossActionEvaluation_slice, coordinateLift_original]

/-- Summary: `H` is complete and finite-dimensional over `L`, the joint action is analytic,
and the bad coordinate has a bounded lift. -/
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
