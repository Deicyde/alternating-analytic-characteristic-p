import AlternatingAnalytic.Analysis.DeterminantPairScalars
import AlternatingAnalytic.Analysis.RigidDenseSourceConcrete
import AlternatingAnalytic.Analysis.WeightedDeterminantBound
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import AlternatingAnalytic.Analysis.DeterminantCoefficientSpan

/-! Literal maximum-norm padding of the determinant pair, including zero auxiliary coordinates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators NNReal
namespace AlternatingAnalytic.DeterminantPair.Padding

variable (p : ℕ) [Fact p.Prime] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] (n : ℕ)

local instance preferredNormedFieldK : NormedField (K p r) :=
  (inferInstance : NontriviallyNormedField (K p r)).toNormedField
local instance preferredFieldK : Field (K p r) :=
  (inferInstance : NontriviallyNormedField (K p r)).toField
local instance preferredFieldL : Field (L p r) :=
  (inferInstance : NontriviallyNormedField (L p r)).toField

abbrev E := RigidDenseSource.Concrete.source p r × (Fin n → K p r)
abbrev D := DeterminantPair.D p r × (Fin n → K p r)
abbrev H := A p r × (Fin n → L p r)

/-- Coordinatewise inclusion, valid also for the empty function space. -/
def auxiliaryInclusion : (Fin n → K p r) →ₗᵢ[K p r] (Fin n → L p r) where
  __ := RigidDenseSource.coordinateMap (K p r) (L p r) (Fin n)
  norm_map' x := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
      intro i
      simpa only [RigidDenseSource.coordinateMap_apply, norm_algebraMap'] using norm_le_pi_norm x i
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      intro i
      simpa only [RigidDenseSource.coordinateMap_apply, norm_algebraMap'] using
        norm_le_pi_norm (RigidDenseSource.coordinateMap (K p r) (L p r) (Fin n) x) i

@[simp] theorem auxiliaryInclusion_apply (x : Fin n → K p r) (i : Fin n) :
    auxiliaryInclusion p r n x i = algebraMap (K p r) (L p r) (x i) := rfl

theorem denseRange_auxiliaryInclusion : DenseRange (auxiliaryInclusion p r n) :=
  DenseRange.piMap fun _ => RationalField.denseRange_algebraMap (ZMod p) r

/-- The literal dense isometric inclusion of the padded rigid source. -/
def inclusionE : E p r n →ₗᵢ[K p r] H p r n where
  __ := (RigidDenseSource.Concrete.source p r).subtype.prodMap
    (auxiliaryInclusion p r n).toLinearMap
  norm_map' x := by
    change max ‖(x.1 : A p r)‖ ‖auxiliaryInclusion p r n x.2‖ = max ‖x.1‖ ‖x.2‖
    rw [(auxiliaryInclusion p r n).norm_map]
    rfl

/-- The literal dense isometric inclusion of the padded determinant source. -/
def inclusionD : D p r n →ₗᵢ[K p r] H p r n where
  __ := (DeterminantPair.D p r).subtype.prodMap (auxiliaryInclusion p r n).toLinearMap
  norm_map' x := by
    change max ‖(x.1 : A p r)‖ ‖auxiliaryInclusion p r n x.2‖ = max ‖x.1‖ ‖x.2‖
    rw [(auxiliaryInclusion p r n).norm_map]
    rfl

@[simp] theorem inclusionE_apply (x : E p r n) :
    inclusionE p r n x = ((x.1 : A p r), fun i => algebraMap (K p r) (L p r) (x.2 i)) := rfl

@[simp] theorem inclusionD_apply (x : D p r n) :
    inclusionD p r n x = ((x.1 : A p r), fun i => algebraMap (K p r) (L p r) (x.2 i)) := rfl

theorem denseRange_inclusionE : DenseRange (inclusionE p r n) :=
  (RigidDenseSource.Concrete.denseRange_subtype p r).prodMap
    (denseRange_auxiliaryInclusion p r n)

theorem denseRange_inclusionD : DenseRange (inclusionD p r n) :=
  (DeterminantPair.denseRange_D_subtype p r).prodMap (denseRange_auxiliaryInclusion p r n)

/-- The ordered standard basis has the original p coordinates first. -/
def basis : Module.Basis (Fin (p + n)) (L p r) (H p r n) :=
  ((TruncatedPolynomial.basis (L p r) p).prod (Pi.basisFun (L p r) (Fin n))).reindex
    finSumFinEquiv

@[simp] theorem basis_castAdd (i : Fin p) :
    basis p r n (Fin.castAdd n i) = (e p r i, 0) := by
  simp [basis, Module.Basis.reindex_apply, Module.Basis.prod_apply, e]

@[simp] theorem basis_natAdd (i : Fin n) :
    basis p r n (Fin.natAdd p i) = (0, Pi.single i 1) := by
  simp [basis, Module.Basis.reindex_apply, Module.Basis.prod_apply, Pi.basisFun_apply]

def standardE (i : Fin (p + n)) : E p r n :=
  Sum.elim (fun j => (RigidDenseSource.Concrete.standard p r j, 0))
    (fun j => (0, Pi.single j 1)) (finSumFinEquiv.symm i)

def standardD (i : Fin (p + n)) : D p r n :=
  Sum.elim (fun j => (⟨e p r j, e_mem_D p r j⟩, 0))
    (fun j => (0, Pi.single j 1)) (finSumFinEquiv.symm i)

@[simp] theorem inclusionE_standardE (i : Fin (p + n)) :
    inclusionE p r n (standardE p r n i) = basis p r n i := by
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  cases i with
  | inl i => simp [standardE, e_eq_epsilon_pow]; rfl
  | inr i =>
      ext j <;> simp [standardE, Pi.single_apply, apply_ite]

@[simp] theorem inclusionD_standardD (i : Fin (p + n)) :
    inclusionD p r n (standardD p r n i) = basis p r n i := by
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  cases i with
  | inl i => simp [standardD]; rfl
  | inr i =>
      ext j <;> simp [standardD, Pi.single_apply, apply_ite]

@[simp] theorem norm_basis (i : Fin (p + n)) : ‖basis p r n i‖ = 1 := by
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  cases i <;> simp [Prod.norm_def, e, Pi.norm_single]

@[simp] theorem norm_standardE (i : Fin (p + n)) : ‖standardE p r n i‖ = 1 := by
  rw [← (inclusionE p r n).norm_map, inclusionE_standardE, norm_basis]

@[simp] theorem norm_standardD (i : Fin (p + n)) : ‖standardD p r n i‖ = 1 := by
  rw [← (inclusionD p r n).norm_map, inclusionD_standardD, norm_basis]

/-- The actual normalized ordered determinant on the complete ambient product. -/
def delta : (Fin (p + n) → H p r n) → L p r := (basis p r n).det

@[simp] theorem delta_basis : delta p r n (basis p r n) = 1 :=
  (basis p r n).det_self

@[simp] theorem delta_standardE :
    delta p r n (fun i => inclusionE p r n (standardE p r n i)) = 1 := by simp only [inclusionE_standardE, delta_basis]

@[simp] theorem delta_standardD :
    delta p r n (fun i => inclusionD p r n (standardD p r n i)) = 1 := by simp only [inclusionD_standardD, delta_basis]

theorem norm_repr_le (x : H p r n) (i : Fin (p + n)) :
    ‖(basis p r n).repr x i‖ ≤ ‖x‖ := by
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  cases i with
  | inl i =>
      simp only [basis, Module.Basis.repr_reindex_apply, Equiv.symm_apply_apply,
        Module.Basis.prod_repr_inl]
      exact (TruncatedPolynomial.norm_coefficient_le (L p r) p x.1 i).trans
        (le_max_left _ _)
  | inr i =>
      simp only [basis, Module.Basis.repr_reindex_apply, Equiv.symm_apply_apply,
        Module.Basis.prod_repr_inr, Pi.basisFun_repr]
      exact (norm_le_pi_norm x.2 i).trans (le_max_right _ _)

/-- The ambient determinant has no factorial loss in the literal maximum norm. -/
theorem norm_delta_le (x : Fin (p + n) → H p r n) :
    ‖delta p r n x‖ ≤ ∏ i, ‖x i‖ := by
  simpa [delta, Module.Basis.det_apply] using
    norm_det_mul_prod_le ((basis p r n).toMatrix x) (fun _ => 1) (fun j => ‖x j‖)
      (fun _ => zero_le_one) (fun i j => by simpa only [Module.Basis.toMatrix_apply, mul_one] using norm_repr_le p r n (x j) i)

theorem norm_delta_inclusionE_le (x : Fin (p + n) → E p r n) :
    ‖delta p r n (fun i => inclusionE p r n (x i))‖ ≤ ∏ i, ‖x i‖ := by
  simpa only [LinearIsometry.norm_map] using norm_delta_le p r n (fun i => inclusionE p r n (x i))

theorem norm_delta_inclusionD_le (x : Fin (p + n) → D p r n) :
    ‖delta p r n (fun i => inclusionD p r n (x i))‖ ≤ ∏ i, ‖x i‖ := by
  simpa only [LinearIsometry.norm_map] using norm_delta_le p r n (fun i => inclusionD p r n (x i))

@[simp] theorem repr_castAdd (x : H p r n) (i : Fin p) :
    (basis p r n).repr x (Fin.castAdd n i) = TruncatedPolynomial.coeff (L p r) p x.1 i := by
  simp [basis, TruncatedPolynomial.coeff,
    Module.Basis.equivFun_apply]

@[simp] theorem repr_natAdd (x : H p r n) (i : Fin n) :
    (basis p r n).repr x (Fin.natAdd p i) = x.2 i := by
  simp [basis]

theorem repr_castSucc (x : H p r (n + 1)) (i : Fin (p + n)) :
    (basis p r (n + 1)).repr x i.castSucc =
      (basis p r n).repr (x.1, fun j => x.2 j.castSucc) i := by
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  cases i with
  | inl i => simp only [finSumFinEquiv_apply_left, Fin.castSucc_castAdd, repr_castAdd]
  | inr i =>
      change (basis p r (n + 1)).repr x (Fin.natAdd p i.castSucc) = _
      rw [repr_natAdd]
      simp only [finSumFinEquiv_apply_right, repr_natAdd]

@[simp] theorem repr_last (x : H p r (n + 1)) :
    (basis p r (n + 1)).repr x (Fin.last (p + n)) = x.2 (Fin.last n) := by
  change (basis p r (n + 1)).repr x (Fin.natAdd p (Fin.last n)) = _
  exact repr_natAdd p r (n+1) x (Fin.last n)

/-- Laplace expansion along the last auxiliary coordinate reduces padding by one. -/
theorem delta_succ (x : Fin (p + (n + 1)) → H p r (n + 1)) :
    delta p r (n + 1) x = ∑ j : Fin (p + n + 1),
      (-1 : L p r) ^ ((p + n) + (j : ℕ)) * (x j).2 (Fin.last n) *
        delta p r n (fun i => ((x (j.succAbove i)).1,
          fun k => (x (j.succAbove i)).2 k.castSucc)) := by
  rw [delta, Module.Basis.det_apply, Matrix.det_succ_row _ (Fin.last (p+n))]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Fin.val_last, Module.Basis.toMatrix_apply, repr_last]
  congr 1
  unfold delta
  rw [Module.Basis.det_apply]
  congr 1
  ext i k
  simp only [Matrix.submatrix_apply, Module.Basis.toMatrix_apply,
    Fin.succAbove_last, repr_castSucc]

/-- Algebraic padding preserves every scalar submodule containing the original
p-fold determinant values. No completeness or L-module structure is used. -/
theorem delta_mem_of_unpadded (S : Submodule (K p r) (A p r))
    (T : Submodule (K p r) (L p r))
    (h : ∀ x : Fin p → S, DeterminantPair.delta p r (fun i => x i) ∈ T)
    (x : Fin (p + n) → S × (Fin n → K p r)) :
    delta p r n (fun i => ((x i).1, fun j => algebraMap (K p r) (L p r) ((x i).2 j))) ∈ T := by
  induction n with
  | zero =>
      have heq : delta p r 0 (fun i => ((x i).1,
          fun j => algebraMap (K p r) (L p r) ((x i).2 j))) =
          DeterminantPair.delta p r (fun i => (x i).1) := by
        rw [delta, Module.Basis.det_apply, DeterminantPair.delta]
        congr 1
        ext i j
        change (basis p r 0).repr _ (Fin.castAdd 0 i) = _
        rw [repr_castAdd]
        rfl
      rw [heq]
      exact h (fun i => (x i).1)
  | succ n ih =>
      rw [delta_succ]
      apply T.sum_mem
      intro j _
      have hminor := ih (fun i => ((x (j.succAbove i)).1,
        fun k => (x (j.succAbove i)).2 k.castSucc))
      convert T.smul_mem ((-1 : K p r) ^ ((p+n)+(j : ℕ)) *
        (x j).2 (Fin.last n)) hminor using 1;
        simp only [Algebra.smul_def, map_mul, map_pow, map_neg, map_one]

/-- The padded determinant on the literal D product takes values in the original G. -/
theorem delta_inclusionD_mem (x : Fin (p+n) → D p r n) :
    delta p r n (fun i => inclusionD p r n (x i)) ∈ G p r := by
  apply delta_mem_of_unpadded p r n (DeterminantPair.D p r) (G p r)
  intro y
  exact Submodule.subset_span ⟨y, rfl⟩

/-- Adjoin the auxiliary standard vectors after an arbitrary original tuple. -/
def padTuple (S : Submodule (K p r) (A p r)) (x : Fin p → S) :
    Fin (p+n) → S × (Fin n → K p r) :=
  fun i => Sum.elim (fun j => (x j, 0)) (fun j => (0, Pi.single j 1))
    (finSumFinEquiv.symm i)

@[simp] theorem padTuple_castAdd (S : Submodule (K p r) (A p r))
    (x : Fin p → S) (i : Fin p) : padTuple p r n S x (Fin.castAdd n i) = (x i, 0) := by
  simp [padTuple]

@[simp] theorem padTuple_natAdd (S : Submodule (K p r) (A p r))
    (x : Fin p → S) (i : Fin n) : padTuple p r n S x (Fin.natAdd p i) = (0, Pi.single i 1) := by
  simp [padTuple]

/-- The block diagonal determinant identity includes the empty auxiliary block. -/
theorem delta_padTuple (S : Submodule (K p r) (A p r)) (x : Fin p → S) :
    delta p r n (fun i => ((padTuple p r n S x i).1,
      fun j => algebraMap (K p r) (L p r) ((padTuple p r n S x i).2 j))) =
      DeterminantPair.delta p r (fun i => x i) := by
  rw [delta, Module.Basis.det_apply,
    ← Matrix.det_reindex_self finSumFinEquiv.symm]
  have hmat : Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm
      ((basis p r n).toMatrix (fun i => ((padTuple p r n S x i).1,
        fun j => algebraMap (K p r) (L p r) ((padTuple p r n S x i).2 j)))) =
      Matrix.fromBlocks
        (fun i j => TruncatedPolynomial.coeff (L p r) p (x j) i) 0 0
        (1 : Matrix (Fin n) (Fin n) (L p r)) := by
    ext i j
    cases i <;> cases j <;>
      simp [Matrix.reindex_apply, Module.Basis.toMatrix_apply,
        Matrix.fromBlocks, Pi.single_apply, Matrix.one_apply, eq_comm]
  rw [hmat, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]
  rfl

/-- Adjoining finitely many rational coordinates leaves the determinant-value
span unchanged, even for zero auxiliary coordinates. -/
theorem span_delta_eq_unpadded (S : Submodule (K p r) (A p r)) :
    Submodule.span (K p r) (Set.range (fun x : Fin (p+n) → S × (Fin n → K p r) =>
      delta p r n (fun i => ((x i).1,
        fun j => algebraMap (K p r) (L p r) ((x i).2 j))))) =
    Submodule.span (K p r) (Set.range (fun x : Fin p → S =>
      DeterminantPair.delta p r (fun i => x i))) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    exact delta_mem_of_unpadded p r n S _
      (fun y => Submodule.subset_span (Set.mem_range_self y)) x
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    change DeterminantPair.delta p r (fun i => x i) ∈ _
    rw [← delta_padTuple p r n S x]
    exact Submodule.subset_span ⟨padTuple p r n S x, rfl⟩

/-- The padded scalar determinant-value space is exactly the original primary span. -/
theorem span_delta_E :
    Submodule.span (K p r) (Set.range (fun x : Fin (p+n) → E p r n =>
      delta p r n (fun i => inclusionE p r n (x i)))) = primarySpan p r := by
  rw [show (fun x : Fin (p+n) → E p r n => delta p r n (fun i => inclusionE p r n (x i))) =
    (fun x : Fin (p+n) → RigidDenseSource.Concrete.source p r × (Fin n → K p r) =>
      delta p r n (fun i => ((x i).1,
        fun j => algebraMap (K p r) (L p r) ((x i).2 j)))) from rfl]
  rw [span_delta_eq_unpadded, delta_span_E]

/-- Restriction of the actual ambient determinant to rational scalars. -/
def determinantK : H p r n [⋀^Fin (p+n)]→ₗ[K p r] L p r where
  __ := ((basis p r n).det.toMultilinearMap).restrictScalars (K p r)
  map_eq_zero_of_eq' v _i _j hv hij := (basis p r n).det.map_eq_zero_of_eq v hv hij

/-- The actual G-valued normalized determinant on the padded D carrier. -/
def determinantD : D p r n [⋀^Fin (p+n)]→L[K p r] G p r :=
  (((determinantK p r n).compLinearMap (inclusionD p r n).toLinearMap).codRestrict
    (G p r) (delta_inclusionD_mem p r n)).mkContinuous 1
      (fun x => by
        change ‖delta p r n (fun i => inclusionD p r n (x i))‖ ≤ 1 * ∏ i, ‖x i‖
        simpa only [one_mul] using norm_delta_inclusionD_le p r n x)

@[simp] theorem determinantD_apply (x : Fin (p+n) → D p r n) :
    (determinantD p r n x : L p r) = delta p r n (fun i => inclusionD p r n (x i)) := rfl

@[simp] theorem determinantD_standard :
    (determinantD p r n (standardD p r n) : L p r) = 1 := by
  rw [determinantD_apply, delta_standardD]

@[simp] theorem norm_determinantD : ‖determinantD p r n‖ = 1 := by
  apply le_antisymm
  · apply (determinantD p r n).opNorm_le_bound zero_le_one
    intro x
    change ‖delta p r n (fun i => inclusionD p r n (x i))‖ ≤ 1 * ∏ i, ‖x i‖
    simpa only [one_mul] using norm_delta_inclusionD_le p r n x
  · have h := (determinantD p r n).le_opNorm (standardD p r n)
    have hnorm : ‖determinantD p r n (standardD p r n)‖ = 1 := by
      change ‖(determinantD p r n (standardD p r n) : L p r)‖ = 1
      rw [determinantD_standard, norm_one]
    simpa only [hnorm, norm_standardD, Finset.prod_const_one, mul_one] using h

theorem norm_E (x : E p r n) : ‖x‖ = max ‖x.1‖ ‖x.2‖ := rfl
theorem norm_D (x : D p r n) : ‖x‖ = max ‖x.1‖ ‖x.2‖ := rfl
theorem norm_H (x : H p r n) : ‖x‖ = max ‖x.1‖ ‖x.2‖ := rfl

end AlternatingAnalytic.DeterminantPair.Padding
