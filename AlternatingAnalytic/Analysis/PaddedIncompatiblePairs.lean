import AlternatingAnalytic.Analysis.DeterminantPairSelfActions
import AlternatingAnalytic.Analysis.PaddedSelfAction
import AlternatingAnalytic.Analysis.PaddedSplitCanonical
import AlternatingAnalytic.Analysis.PaddedCrossAction
import AlternatingAnalytic.Analysis.PaddedCompletions

/-!
# Padded pairs in every degree `k ≥ p`

The objects `X_k = (E_k, G)` and `Y_k = (D_k, G)` of Theorem H.4, with `E_k = E × Kⁿ`,
`D_k = D × Kⁿ`, maximum norms and `n = k - p`: both self-actions are analytic, `Y_k` is split,
and the cross-action from `Y_k` to `X_k` is not analytic.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators NNReal

namespace AlternatingAnalytic.DeterminantPair.Padding

variable (p : ℕ) [Fact p.Prime] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] (n : ℕ)
attribute [local instance] DeterminantPair.preferredNormedFieldK
  DeterminantPair.preferredFieldK DeterminantPair.preferredFieldL

/-- The padded pairs in degree `p + n`: norms, the coefficient isometry, the block form of
endomorphisms, analytic self-actions, the split retraction, and the nonanalytic cross-action.
`n = 0` is allowed. -/
theorem padded_split_pairs_with_incompatible_analytic_self_actions :
    (∀ x : E p r n, ‖x‖ = max ‖x.1‖ ‖x.2‖) ∧
    (∀ x : D p r n, ‖x‖ = max ‖x.1‖ ‖x.2‖) ∧
    (∀ x : G p r, ‖x‖ = ‖(x : L p r)‖) ∧
    Isometry (paddedCoefficientEquiv p r n) ∧
    (∀ (m : E p r n [⋀^Fin (p+n)]→L[K p r] G p r) (x : Fin (p+n) → E p r n),
      (m x : L p r) = (paddedCoefficientEquiv p r n m : L p r) *
        delta p r n (fun i => inclusionE p r n (x i))) ∧
    (determinantD p r n (standardD p r n) : L p r) = 1 ∧
    (∀ (u : E p r n →L[K p r] E p r n) (x : E p r n),
      completedEndomorphism p r n u (inclusionE p r n x) = inclusionE p r n (u x)) ∧
    (∀ (u : E p r n →L[K p r] E p r n) (x : DeterminantPair.E p r),
      (u (x, 0)).1 = scalarCoordinate p r n u • x ∧ (u (x, 0)).2 = 0) ∧
    (∀ u : E p r n →L[K p r] E p r n,
      scalarCoordinate p r n u = RigidDenseSource.Concrete.endScalarEquiv p r
        ((ContinuousLinearMap.fst (K p r) (DeterminantPair.E p r) (Fin n → K p r)).comp
          (u.comp (ContinuousLinearMap.inl (K p r) (DeterminantPair.E p r) (Fin n → K p r))))) ∧
    (∀ (u : E p r n →L[K p r] E p r n) (i j : Fin n),
      auxiliaryCoordinate p r n i j u = (u (0, Pi.single j 1)).2 i) ∧
    (∀ u : E p r n →L[K p r] E p r n,
      Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm
        (LinearMap.toMatrix (basis p r n) (basis p r n)
          (completedEndomorphism p r n u).toLinearMap) =
        Matrix.fromBlocks
          (algebraMap (K p r) (L p r) (scalarCoordinate p r n u) •
            (1 : Matrix (Fin p) (Fin p) (L p r)))
          (upperRightMatrix p r n u) 0
          ((algebraMap (K p r) (L p r)).mapMatrix (auxiliaryMatrix p r n u))) ∧
    (∀ u : E p r n →L[K p r] E p r n,
      LinearMap.det (completedEndomorphism p r n u).toLinearMap =
        algebraMap (K p r) (L p r)
          ((scalarCoordinate p r n u) ^ p * (auxiliaryMatrix p r n u).det)) ∧
    (∀ h : (E p r n →L[K p r] E p r n) × (G p r →L[K p r] G p r),
      alternatingMapAction (p+n) h = determinantFactor p r n h.1 •
        ContinuousLinearMap.compContinuousAlternatingMapCLM (K p r) (E p r n)
          (G p r) (G p r) (Fin (p+n)) h.2) ∧
    AnalyticOnNhd (K p r)
      (alternatingMapAction (K := K p r) (E := E p r n) (E' := E p r n)
        (F := G p r) (F' := G p r) (p+n)) Set.univ ∧
    (∀ (m : D p r n [×(p+n)]→L[K p r] G p r) (x : Fin p → DeterminantPair.D p r),
      freezeAuxiliaryLast p r n m x = m (padTuple p r n (DeterminantPair.D p r) x)) ∧
    canonicalRetraction p r n = (iteratedWedgeLast p r n).comp
      ((DeterminantPair.retractionR p r).comp (freezeAuxiliaryLast p r n)) ∧
    (∀ m : D p r n [⋀^Fin (p+n)]→L[K p r] G p r,
      canonicalRetraction p r n m.toContinuousMultilinearMap = m) ∧
    IsSplitAlternatingPair (K p r) (p+n) (D p r n) (G p r) ∧
    AnalyticOnNhd (K p r)
      (alternatingMapAction (K := K p r) (E := D p r n) (E' := D p r n)
        (F := G p r) (F' := G p r) (p+n)) Set.univ ∧
    (∀ x : DeterminantPair.E p r,
      paddedMultiplication p r n x = multiplicationLinearPart p r n x + auxiliaryIdentity p r n) ∧
    (∀ x : DeterminantPair.E p r,
      crossActionEvaluation p r n (alternatingMapAction (p+n) (crossActionSlice p r n x)) =
        determinantCoordinate p r x) ∧
    (∀ x : DeterminantPair.E p r,
      (crossActionEvaluation p r n
        (alternatingMapAction (p+n) (crossActionSlice p r n x)) : L p r) =
          TruncatedPolynomial.coeff (L p r) p (x : A p r) 0 ^ p) ∧
    ¬ AnalyticAt (K p r)
      (alternatingMapAction (K := K p r) (E := D p r n) (E' := E p r n)
        (F := G p r) (F' := G p r) (p+n))
      (auxiliaryIdentity p r n, ContinuousLinearMap.id (K p r) (G p r)) ∧
    FiniteDimensional (K p r) (E p r n) ∧ FiniteDimensional (K p r) (D p r n) ∧
    FiniteDimensional (K p r) (G p r) ∧
    Module.finrank (K p r) (E p r n) = p + 1 + n ∧
    IsUltrametricDist (E p r n) ∧ IsUltrametricDist (D p r n) ∧ IsUltrametricDist (G p r) := by
  refine ⟨norm_E p r n, norm_D p r n, DeterminantPair.norm_G p r,
    (paddedCoefficientEquiv p r n).isometry,
    paddedCoefficientEquiv_pointwise p r n, determinantD_standard p r n,
    completedEndomorphism_apply p r n,
    (fun u x => ⟨sourceBlock_apply p r n u x, lowerLeft_eq_zero p r n u x⟩),
    scalarCoordinate_apply p r n, auxiliaryCoordinate_apply p r n,
    completedEndomorphism_matrix p r n, det_completedEndomorphism p r n,
    selfActionE_eq p r n, (fun h _ => analyticAt_selfActionE p r n h),
    freezeAuxiliaryLast_apply p r n, rfl, canonicalRetraction_fix p r n,
    isSplitAlternatingPair_canonical p r n, ?_, paddedMultiplication_eq_affine p r n,
    crossActionEvaluation_slice p r n, ?_, not_analyticAt_crossAction p r n,
    inferInstance, inferInstance, inferInstance, finrank_E p r n,
    inferInstance, inferInstance, inferInstance⟩
  · exact analyticOnNhd_alternatingMapAction_of_split_destination (p+n)
      (isSplitAlternatingPair_canonical p r n)
  · intro x
    rw [crossActionEvaluation_slice, determinantCoordinate_scalar]

/-- The completion identifications of `PaddedCompletions`. -/
theorem concrete_completion_identifications :
    Isometry (inclusionE p r n) ∧ DenseRange (inclusionE p r n) ∧
    Isometry (inclusionD p r n) ∧ DenseRange (inclusionD p r n) ∧
    Isometry (G p r).subtypeₗᵢ ∧ DenseRange (G p r).subtypeₗᵢ ∧
    Isometry (C p r).subtypeₗᵢ ∧ DenseRange (C p r).subtypeₗᵢ ∧
    (∀ a : K p r, algebraMap (K p r) (L p r) a ∈ C p r) ∧
    (∀ x : E p r n,
      completionE p r n (x : UniformSpace.Completion (E p r n)) = inclusionE p r n x) ∧
    (∀ x : D p r n,
      completionD p r n (x : UniformSpace.Completion (D p r n)) = inclusionD p r n x) ∧
    (∀ x : G p r,
      DeterminantPair.completionG p r (x : UniformSpace.Completion (G p r)) = (x : L p r)) ∧
    (∀ x : C p r,
      completionC p r (x : UniformSpace.Completion (C p r)) = (x : L p r)) ∧
    CompleteSpace (H p r n) ∧ FiniteDimensional (L p r) (H p r n) ∧
    Module.finrank (L p r) (H p r n) = p + n ∧
    (∀ (a : L p r) (x : H p r n), ‖a • x‖ = ‖a‖ * ‖x‖) ∧ CompleteSpace (L p r) :=
  concrete_completions p r n

/-- For every `k ≥ p`, with `n = k - p`: `K` is not complete, the pairs are finite-dimensional
and nonarchimedean, `Y_k` is split, both self-actions are analytic, and the cross-action is not
analytic. -/
theorem realized_pairs_for_every_degree (k : ℕ) (hpk : p ≤ k) :
    p + (k-p) = k ∧ ¬ CompleteSpace (K p r) ∧
    FiniteDimensional (K p r) (E p r (k-p)) ∧
    FiniteDimensional (K p r) (D p r (k-p)) ∧ FiniteDimensional (K p r) (G p r) ∧
    IsUltrametricDist (E p r (k-p)) ∧ IsUltrametricDist (D p r (k-p)) ∧
    IsUltrametricDist (G p r) ∧
    Isometry (paddedCoefficientEquiv p r (k-p)) ∧
    IsSplitAlternatingPair (K p r) k (D p r (k-p)) (G p r) ∧
    AnalyticOnNhd (K p r)
      (alternatingMapAction (K := K p r) (E := E p r (k-p)) (E' := E p r (k-p))
        (F := G p r) (F' := G p r) k) Set.univ ∧
    AnalyticOnNhd (K p r)
      (alternatingMapAction (K := K p r) (E := D p r (k-p)) (E' := D p r (k-p))
        (F := G p r) (F' := G p r) k) Set.univ ∧
    (∀ x : DeterminantPair.E p r,
      crossActionEvaluation p r (k-p)
        (alternatingMapAction (p+(k-p)) (crossActionSlice p r (k-p) x)) =
          determinantCoordinate p r x) ∧
    ¬ AnalyticAt (K p r)
      (alternatingMapAction (K := K p r) (E := D p r (k-p)) (E' := E p r (k-p))
        (F := G p r) (F' := G p r) k)
      (auxiliaryIdentity p r (k-p), ContinuousLinearMap.id (K p r) (G p r)) := by
  have hk : p + (k-p) = k := Nat.add_sub_of_le hpk
  generalize hn : k-p = n at *
  subst k
  refine ⟨rfl, RationalField.not_completeSpace (ZMod p) r,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    (paddedCoefficientEquiv p r n).isometry, isSplitAlternatingPair_canonical p r n,
    (fun h _ => analyticAt_selfActionE p r n h), ?_,
    crossActionEvaluation_slice p r n, not_analyticAt_crossAction p r n⟩
  exact analyticOnNhd_alternatingMapAction_of_split_destination (p+n)
    (isSplitAlternatingPair_canonical p r n)

end AlternatingAnalytic.DeterminantPair.Padding
