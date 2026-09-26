import AlternatingAnalytic.Analysis.DeterminantCoefficientSpaces
import AlternatingAnalytic.Analysis.AnalyticFamilies

/-! The genuine self-action of each maximum-norm padded rigid source. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped BigOperators NNReal
namespace AlternatingAnalytic.DeterminantPair.Padding

variable (p : ℕ) [Fact p.Prime] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] (n : ℕ)
attribute [local instance] preferredNormedFieldK preferredFieldK preferredFieldL

abbrev OriginalE := RigidDenseSource.Concrete.source p r

/-- Bounded extraction of the original-source block by genuine product maps. -/
def sourceBlock : (E p r n →L[K p r] E p r n) →L[K p r]
    (OriginalE p r →L[K p r] OriginalE p r) :=
  (ContinuousLinearMap.compL (K p r) (OriginalE p r) (E p r n) (OriginalE p r)
    (ContinuousLinearMap.fst (K p r) (OriginalE p r) (Fin n → K p r))).comp
    ((ContinuousLinearMap.compL (K p r) (OriginalE p r) (E p r n) (E p r n)).flip
      (ContinuousLinearMap.inl (K p r) (OriginalE p r) (Fin n → K p r)))

/-- The scalar coordinate uses rigidity, rather than algebraic coordinates of E. -/
def scalarCoordinate : (E p r n →L[K p r] E p r n) →L[K p r] K p r :=
  (RigidDenseSource.Concrete.endScalarEquiv p r).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (sourceBlock p r n)

/-- The actual bounded standard matrix coordinate of the auxiliary block. -/
def auxiliaryCoordinate (i j : Fin n) :
    (E p r n →L[K p r] E p r n) →L[K p r] K p r :=
  ((ContinuousLinearMap.proj i).comp
    (ContinuousLinearMap.snd (K p r) (OriginalE p r) (Fin n → K p r))).comp
    (ContinuousLinearMap.apply (K p r) (E p r n) (0, Pi.single j 1))

@[simp] theorem scalarCoordinate_apply (u : E p r n →L[K p r] E p r n) :
    scalarCoordinate p r n u = RigidDenseSource.Concrete.endScalarEquiv p r
      ((ContinuousLinearMap.fst (K p r) (OriginalE p r) (Fin n → K p r)).comp
        (u.comp (ContinuousLinearMap.inl (K p r) (OriginalE p r) (Fin n → K p r)))) := rfl

@[simp] theorem auxiliaryCoordinate_apply (u : E p r n →L[K p r] E p r n)
    (i j : Fin n) : auxiliaryCoordinate p r n i j u = (u (0, Pi.single j 1)).2 i := rfl

theorem sourceBlock_apply (u : E p r n →L[K p r] E p r n) (x : OriginalE p r) :
    (u (x, 0)).1 = scalarCoordinate p r n u • x :=
  RigidDenseSource.Concrete.endScalarEquiv_apply p r (sourceBlock p r n u) x

/-- Vanishing is proved separately for each bounded auxiliary functional. -/
theorem lowerLeft_eq_zero (u : E p r n →L[K p r] E p r n) (x : OriginalE p r) :
    (u (x, 0)).2 = 0 := by
  ext i
  let f : OriginalE p r →L[K p r] K p r :=
    (ContinuousLinearMap.proj i).comp
      ((ContinuousLinearMap.snd (K p r) (OriginalE p r) (Fin n → K p r)).comp
        (u.comp (ContinuousLinearMap.inl (K p r) (OriginalE p r) (Fin n → K p r))))
  exact congrArg (fun g : OriginalE p r →L[K p r] K p r => g x)
    (RigidDenseSource.Concrete.dual_eq_zero p r f)

/-- Extend only into the complete ambient product, then promote to L-linearity. -/
def completedEndomorphism (u : E p r n →L[K p r] E p r n) :
    H p r n →L[L p r] H p r n :=
  denseScalarLinearExtension (RationalField.denseRange_algebraMap (ZMod p) r)
    (denseLinearExtension (inclusionE p r n) (denseRange_inclusionE p r n)
      ((inclusionE p r n).toContinuousLinearMap.comp u))

@[simp] theorem completedEndomorphism_apply (u : E p r n →L[K p r] E p r n)
    (x : E p r n) :
    completedEndomorphism p r n u (inclusionE p r n x) = inclusionE p r n (u x) :=
  denseLinearExtension_apply (inclusionE p r n) (denseRange_inclusionE p r n) _ x

/-- Upper-right coefficients live in L; no K-coordinate functional of E is used. -/
def upperRightMatrix (u : E p r n →L[K p r] E p r n) :
    Matrix (Fin p) (Fin n) (L p r) :=
  fun i j => TruncatedPolynomial.coeff (L p r) p (u (0, Pi.single j 1)).1 i

def auxiliaryMatrix (u : E p r n →L[K p r] E p r n) :
    Matrix (Fin n) (Fin n) (K p r) := fun i j => auxiliaryCoordinate p r n i j u

@[simp] theorem standardE_castAdd (i : Fin p) :
    standardE p r n (Fin.castAdd n i) = (RigidDenseSource.Concrete.standard p r i, 0) := by
  simp [standardE]

@[simp] theorem standardE_natAdd (i : Fin n) :
    standardE p r n (Fin.natAdd p i) = (0, Pi.single i 1) := by
  simp [standardE]

/-- In the ordered standard basis the extension has the required upper-triangular blocks. -/
theorem completedEndomorphism_matrix (u : E p r n →L[K p r] E p r n) :
    Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm
      (LinearMap.toMatrix (basis p r n) (basis p r n)
        (completedEndomorphism p r n u).toLinearMap) =
    Matrix.fromBlocks
      (algebraMap (K p r) (L p r) (scalarCoordinate p r n u) •
        (1 : Matrix (Fin p) (Fin p) (L p r)))
      (upperRightMatrix p r n u) 0
      ((algebraMap (K p r) (L p r)).mapMatrix (auxiliaryMatrix p r n u)) := by
  classical
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
    LinearMap.toMatrix_apply]
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          change (basis p r n).repr
            (completedEndomorphism p r n u (basis p r n (Fin.castAdd n j)))
              (Fin.castAdd n i) = _
          rw [← inclusionE_standardE, completedEndomorphism_apply, standardE_castAdd,
            repr_castAdd]
          change TruncatedPolynomial.coeff (L p r) p (u
            (RigidDenseSource.Concrete.standard p r j, 0)).1 i = _
          rw [sourceBlock_apply]
          change TruncatedPolynomial.coeff (L p r) p
            ((scalarCoordinate p r n u) •
              (RigidDenseSource.Concrete.standard p r j : A p r)) i = _
          have hj : (RigidDenseSource.Concrete.standard p r j : A p r) = e p r j :=
            subtype_standard p r j
          rw [← algebraMap_smul (L p r), map_smul, hj]
          simp [Matrix.smul_apply, Matrix.one_apply, e, TruncatedPolynomial.coeff_basis,
            eq_comm]
      | inr j =>
          change (basis p r n).repr
            (completedEndomorphism p r n u (basis p r n (Fin.natAdd p j)))
              (Fin.castAdd n i) = _
          rw [← inclusionE_standardE, completedEndomorphism_apply, standardE_natAdd,
            repr_castAdd]
          rfl
  | inr i =>
      cases j with
      | inl j =>
          change (basis p r n).repr
            (completedEndomorphism p r n u (basis p r n (Fin.castAdd n j)))
              (Fin.natAdd p i) = _
          rw [← inclusionE_standardE, completedEndomorphism_apply, standardE_castAdd,
            repr_natAdd]
          change algebraMap (K p r) (L p r)
            ((u (RigidDenseSource.Concrete.standard p r j, 0)).2 i) = 0
          rw [lowerLeft_eq_zero]
          exact map_zero _
      | inr j =>
          change (basis p r n).repr
            (completedEndomorphism p r n u (basis p r n (Fin.natAdd p j)))
              (Fin.natAdd p i) = _
          rw [← inclusionE_standardE, completedEndomorphism_apply, standardE_natAdd,
            repr_natAdd]
          rfl

/-- The genuine K-valued determinant polynomial of the bounded coordinates. -/
def determinantFactor (u : E p r n →L[K p r] E p r n) : K p r :=
  scalarCoordinate p r n u ^ p * (auxiliaryMatrix p r n u).det

theorem det_completedEndomorphism (u : E p r n →L[K p r] E p r n) :
    LinearMap.det (completedEndomorphism p r n u).toLinearMap =
      algebraMap (K p r) (L p r) (determinantFactor p r n u) := by
  classical
  rw [← LinearMap.det_toMatrix (basis p r n),
    ← Matrix.det_reindex_self finSumFinEquiv.symm,
    completedEndomorphism_matrix, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_smul, Matrix.det_one]
  simp only [determinantFactor, map_mul, map_pow, Fintype.card_fin, mul_one]
  rw [RingHom.map_det]

/-- The determinant identity holds for every ambient tuple. -/
theorem delta_completedEndomorphism (u : E p r n →L[K p r] E p r n)
    (x : Fin (p+n) → H p r n) :
    delta p r n (fun i => completedEndomorphism p r n u (x i)) =
      algebraMap (K p r) (L p r) (determinantFactor p r n u) * delta p r n x := by
  change (basis p r n).det ((completedEndomorphism p r n u).toLinearMap ∘ x) = _
  rw [Module.Basis.det_comp, det_completedEndomorphism]
  rfl

/-- Top-degree pullback is scalar multiplication in the original G-valued form space. -/
theorem pullback_eq_smul (u : E p r n →L[K p r] E p r n)
    (m : E p r n [⋀^Fin (p+n)]→L[K p r] G p r) :
    m.compContinuousLinearMap u = determinantFactor p r n u • m := by
  apply (paddedCoefficientEquiv p r n).injective
  apply Subtype.ext
  rw [map_smul, Submodule.coe_smul_of_tower, paddedCoefficientEquiv_apply]
  change (m (fun i => u (standardE p r n i)) : L p r) = _
  rw [paddedCoefficientEquiv_pointwise]
  have hd : delta p r n (fun i => inclusionE p r n (u (standardE p r n i))) =
      algebraMap (K p r) (L p r) (determinantFactor p r n u) := by
    simp_rw [← completedEndomorphism_apply, inclusionE_standardE]
    rw [delta_completedEndomorphism, delta_basis, mul_one]
  rw [hd, Algebra.smul_def, mul_comm]

/-- The actual joint operator action includes the actual bounded postcomposition family. -/
theorem selfActionE_eq (h : (E p r n →L[K p r] E p r n) ×
    (G p r →L[K p r] G p r)) :
    alternatingMapAction (p+n) h = determinantFactor p r n h.1 •
      ContinuousLinearMap.compContinuousAlternatingMapCLM (K p r) (E p r n)
        (G p r) (G p r) (Fin (p+n)) h.2 := by
  apply ContinuousLinearMap.ext
  intro m
  apply ContinuousAlternatingMap.ext
  intro x
  change h.2 ((m.compContinuousLinearMap h.1) x) = _
  rw [pullback_eq_smul]
  simp

/-- A finite determinant expansion in the genuine bounded coordinates is analytic. -/
theorem analyticAt_determinantFactor (u : E p r n →L[K p r] E p r n) :
    AnalyticAt (K p r) (determinantFactor p r n) u := by
  classical
  apply ((scalarCoordinate p r n).analyticAt u).pow p |>.mul
  simp only [auxiliaryMatrix, Matrix.det_apply']
  apply Finset.analyticAt_fun_sum
  intro σ _
  exact analyticAt_const.mul
    (Finset.analyticAt_fun_prod _ (fun i _ =>
      (auxiliaryCoordinate p r n (σ i) i).analyticAt u))

/-- The existing postcomposition family with the operator norm type made explicit. -/
def selfPostcomposition : (G p r →L[K p r] G p r) →L[K p r]
    ((E p r n [⋀^Fin (p+n)]→L[K p r] G p r) →L[K p r]
      (E p r n [⋀^Fin (p+n)]→L[K p r] G p r)) :=
  ContinuousLinearMap.compContinuousAlternatingMapCLM (K p r) (E p r n)
    (G p r) (G p r) (Fin (p+n))

theorem selfActionE_function_eq :
    (alternatingMapAction (K := K p r) (E := E p r n) (E' := E p r n)
      (F := G p r) (F' := G p r) (p+n)) =
    (fun h : (E p r n →L[K p r] E p r n) × (G p r →L[K p r] G p r) =>
      determinantFactor p r n h.1 • selfPostcomposition p r n h.2) :=
  funext (selfActionE_eq p r n)

/-- Global joint self-action analyticity, with neither K nor G assumed complete. -/
theorem analyticAt_selfActionE (h : (E p r n →L[K p r] E p r n) ×
    (G p r →L[K p r] G p r)) :
    AnalyticAt (K p r)
      (alternatingMapAction (K := K p r) (E := E p r n) (E' := E p r n)
        (F := G p r) (F' := G p r) (p+n)) h := by
  let : IsBoundedSMul (K p r)
      ((E p r n [⋀^Fin (p+n)]→L[K p r] G p r) →L[K p r]
        (E p r n [⋀^Fin (p+n)]→L[K p r] G p r)) :=
    NormedSpace.toIsBoundedSMul (𝕜 := K p r)
      (E := (E p r n [⋀^Fin (p+n)]→L[K p r] G p r) →L[K p r]
        (E p r n [⋀^Fin (p+n)]→L[K p r] G p r))
  have hs : AnalyticAt (K p r)
      (fun z : (E p r n →L[K p r] E p r n) × (G p r →L[K p r] G p r) =>
        determinantFactor p r n z.1) h :=
    (analyticAt_determinantFactor p r n h.1).comp analyticAt_fst
  have hp : AnalyticAt (K p r) (selfPostcomposition p r n) h.2 :=
    ContinuousLinearMap.analyticAt (𝕜 := K p r)
      (E := G p r →L[K p r] G p r)
      (F := (E p r n [⋀^Fin (p+n)]→L[K p r] G p r) →L[K p r]
        (E p r n [⋀^Fin (p+n)]→L[K p r] G p r))
      (selfPostcomposition p r n) h.2
  have hv : AnalyticAt (K p r)
      (fun z : (E p r n →L[K p r] E p r n) × (G p r →L[K p r] G p r) =>
        selfPostcomposition p r n z.2) h := hp.comp analyticAt_snd
  rw [selfActionE_function_eq]
  exact hs.smul hv

/-- The complete self-action statement for each literal padded rigid pair,
including the empty auxiliary block. The maps occurring here are the bounded
coordinate maps and the actual complete-field extension constructed above. -/
theorem padded_analytic_self_action :
    (∀ (u : E p r n →L[K p r] E p r n) (x : E p r n),
      completedEndomorphism p r n u (inclusionE p r n x) = inclusionE p r n (u x)) ∧
    (∀ (u : E p r n →L[K p r] E p r n) (x : OriginalE p r),
      (u (x, 0)).1 = scalarCoordinate p r n u • x ∧ (u (x, 0)).2 = 0) ∧
    (∀ u : E p r n →L[K p r] E p r n,
      scalarCoordinate p r n u = RigidDenseSource.Concrete.endScalarEquiv p r
        ((ContinuousLinearMap.fst (K p r) (OriginalE p r) (Fin n → K p r)).comp
          (u.comp (ContinuousLinearMap.inl (K p r) (OriginalE p r) (Fin n → K p r))))) ∧
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
          (scalarCoordinate p r n u ^ p * (auxiliaryMatrix p r n u).det)) ∧
    (∀ (u : E p r n →L[K p r] E p r n)
        (m : E p r n [⋀^Fin (p+n)]→L[K p r] G p r),
      m.compContinuousLinearMap u = determinantFactor p r n u • m) ∧
    (∀ h : (E p r n →L[K p r] E p r n) × (G p r →L[K p r] G p r),
      alternatingMapAction (p+n) h = determinantFactor p r n h.1 •
        ContinuousLinearMap.compContinuousAlternatingMapCLM (K p r) (E p r n)
          (G p r) (G p r) (Fin (p+n)) h.2) ∧
    (∀ h : (E p r n →L[K p r] E p r n) × (G p r →L[K p r] G p r),
      AnalyticAt (K p r)
        (alternatingMapAction (K := K p r) (E := E p r n) (E' := E p r n)
          (F := G p r) (F' := G p r) (p+n)) h) := by
  exact ⟨completedEndomorphism_apply p r n,
    fun u x => ⟨sourceBlock_apply p r n u x, lowerLeft_eq_zero p r n u x⟩,
    scalarCoordinate_apply p r n, auxiliaryCoordinate_apply p r n,
    completedEndomorphism_matrix p r n, det_completedEndomorphism p r n,
    pullback_eq_smul p r n, selfActionE_eq p r n, analyticAt_selfActionE p r n⟩

end AlternatingAnalytic.DeterminantPair.Padding
