import AlternatingAnalytic.Analysis.RigidDenseSourceConcrete

/-!
# Rigid dense finite-dimensional sources

The collected generic source statement and the literal rational/Laurent realization of
`dom:rigid`. The helper modules construct the source, compare polynomial coefficients, extend
maps only into complete ambient spaces, and construct the scalar-action isometry.
-/

noncomputable section

open scoped BigOperators NNReal

namespace AlternatingAnalytic.RigidDenseSource

/-- All conclusions for the generic source, with its actual inherited norm and scalar coordinates. -/
theorem rigid_source_properties
    {K L I : Type*} [NontriviallyNormedField K] [NontriviallyNormedField L]
    [NormedAlgebra K L] [CompleteSpace L] [Fintype I] [Nonempty I]
    {a : I → L} (hKL : DenseRange (algebraMap K L)) (ha : AlgebraicIndependent K a) :
    letI : DecidableEq I := Classical.decEq I
    source K a = LinearMap.range (coordinateMap K L I) ⊔ K ∙ a ∧
    (∀ x : I → L, x ∈ source K a ↔ ∃ b : I → K, ∃ s : K,
      ∀ i, x i = algebraMap K L (b i) + algebraMap K L s * a i) ∧
    (∀ x : source K a,
      ‖x‖ = (Finset.univ.sup fun i : I => ‖(x : I → L) i‖₊ : ℝ≥0)) ∧
    (∀ i : I, (standard K a i : I → L) = Pi.single i 1 ∧ ‖standard K a i‖ = 1) ∧
    Isometry (source K a).subtypeₗᵢ ∧ DenseRange (source K a).subtypeₗᵢ ∧
    CompleteSpace (I → L) ∧ Module.finrank K (source K a) = Fintype.card I + 1 ∧
    (∀ T : source K a →L[K] source K a, ∃! s : K, ∀ x, T x = s • x) ∧
    (∀ f : source K a →L[K] K, f = 0) ∧
    Isometry (endScalarEquiv hKL ha) ∧
    (∀ (T : source K a →L[K] source K a) (x : source K a),
      T x = endScalarEquiv hKL ha T • x) ∧
    (∀ s : K, (endScalarEquiv hKL ha).symm s =
      s • ContinuousLinearMap.id K (source K a)) ∧
    (∀ T : source K a →L[K] source K a, ‖endScalarEquiv hKL ha T‖ = ‖T‖) ∧
    (∀ s : K, ‖s • ContinuousLinearMap.id K (source K a)‖ = ‖s‖) ∧
    endScalarEquiv hKL ha (ContinuousLinearMap.id K (source K a)) = 1 ∧
    (∀ T U : source K a →L[K] source K a,
      endScalarEquiv hKL ha (T.comp U) = endScalarEquiv hKL ha T * endScalarEquiv hKL ha U) := by
  classical
  refine ⟨rfl, fun _ => mem_source K a, norm_source K a,
    fun i => ⟨coe_standard K a i, norm_standard K a i⟩,
    (source K a).subtypeₗᵢ.isometry, denseRange_subtype hKL, inferInstance,
    finrank_source K a ha, existsUnique_scalar hKL ha, dual_eq_zero hKL ha,
    (endScalarEquiv hKL ha).isometry,
    endScalarEquiv_apply hKL ha, endScalarEquiv_symm_apply hKL ha,
    norm_endScalarEquiv hKL ha, norm_scalar_id,
    endScalarEquiv_id hKL ha, endScalarEquiv_comp hKL ha⟩

namespace Concrete

attribute [local instance] preferredNormedFieldK preferredFieldK preferredFieldL

variable (p : ℕ) [Fact p.Prime] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)]

/-- The collected concrete setup and both conclusions of `dom:rigid`, on the
actual truncated polynomial algebra and the common chosen independent family. -/
theorem rigid_source_properties :
    Countable (K p r) ∧ Uncountable (L p r) ∧ CompleteSpace (L p r) ∧
    Isometry (algebraMap (K p r) (L p r)) ∧
    DenseRange (algebraMap (K p r) (L p r)) ∧
    AlgebraicIndependent (K p r)
      (Sum.elim (a p r)
        (RationalLaurentScalars.tau p r (RationalLaurentScalars.AuxiliaryIndex p))) ∧
    vector p r =
      (∑ i : Fin p, a p r i • TruncatedPolynomial.epsilon (L p r) p ^ (i : ℕ)) ∧
    (∀ x : A p r, x ∈ source p r ↔
      ∃ b : Fin p → K p r, ∃ s : K p r,
        x = (∑ i : Fin p, b i • TruncatedPolynomial.epsilon (L p r) p ^ (i : ℕ)) +
          s • vector p r) ∧
    (∀ i : Fin p,
      TruncatedPolynomial.epsilon (L p r) p ^ (i : ℕ) ∈ source p r ∧
      ‖TruncatedPolynomial.epsilon (L p r) p ^ (i : ℕ)‖ = 1) ∧
    (∀ x : A p r, ‖x‖ = (Finset.univ.sup fun i : Fin p =>
      ‖TruncatedPolynomial.coeff (L p r) p x i‖₊ : ℝ≥0)) ∧
    Isometry (source p r).subtypeₗᵢ ∧
    DenseRange (source p r).subtypeₗᵢ ∧ CompleteSpace (A p r) ∧
    ¬ CompleteSpace (K p r) ∧
    Module.finrank (K p r) (source p r) = p + 1 ∧
    Isometry (sourceEquiv p r) ∧
    (∀ x : source p r, (sourceEquiv p r x : Fin p → L p r) =
      TruncatedPolynomial.coefficientIsometry (L p r) p x) ∧
    (∀ T : source p r →L[K p r] source p r,
      ∃! s : K p r, ∀ x, T x = s • x) ∧
    (∀ f : source p r →L[K p r] K p r, f = 0) ∧
    Isometry (endScalarEquiv p r) ∧
    (∀ (T : source p r →L[K p r] source p r) (x : source p r),
      T x = endScalarEquiv p r T • x) ∧
    (∀ s : K p r, (endScalarEquiv p r).symm s =
      s • ContinuousLinearMap.id (K p r) (source p r)) ∧
    (∀ T : source p r →L[K p r] source p r, ‖endScalarEquiv p r T‖ = ‖T‖) ∧
    (∀ s : K p r, ‖s • ContinuousLinearMap.id (K p r) (source p r)‖ = ‖s‖) ∧
    endScalarEquiv p r (ContinuousLinearMap.id (K p r) (source p r)) = 1 ∧
    (∀ T U : source p r →L[K p r] source p r,
      endScalarEquiv p r (T.comp U) = endScalarEquiv p r T * endScalarEquiv p r U) := by
  refine ⟨inferInstance, laurentField_uncountable (ZMod p) r, inferInstance,
    RationalField.isometry_algebraMap (ZMod p) r,
    RationalField.denseRange_algebraMap (ZMod p) r,
    RationalLaurentScalars.algebraicIndependent_auxiliaryScalars p r,
    vector_expansion p r, mem_source p r, ?_,
    TruncatedPolynomial.norm_eq_max (L p r) p,
    (source p r).subtypeₗᵢ.isometry, denseRange_subtype p r, inferInstance,
    RationalField.not_completeSpace (ZMod p) r, finrank_source p r,
    (sourceEquiv p r).isometry, fun _ => rfl,
    existsUnique_scalar p r, dual_eq_zero p r, (endScalarEquiv p r).isometry,
    endScalarEquiv_apply p r, endScalarEquiv_symm_apply p r,
    norm_endScalarEquiv p r, norm_scalar_id p r,
    endScalarEquiv_id p r, endScalarEquiv_comp p r⟩
  intro i
  exact ⟨coe_standard p r i ▸ (standard p r i).property,
    TruncatedPolynomial.norm_epsilon_pow (L p r) p i⟩

end Concrete

end AlternatingAnalytic.RigidDenseSource
