import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Group.Ultra

/-!
# The maximum coefficient norm on truncated polynomial algebras

The algebra `A = L[ε]/(ε^n)`, modelled as `AdjoinRoot (X ^ n)`, with the maximum norm on
coefficients in the basis `1, ε, …, ε^(n-1)`. Over an ultrametric field this norm is
submultiplicative, so `A` is a normed algebra. In Appendix H it is used with `n = p` and
`L = 𝔽_p((t))`.
-/

noncomputable section
open scoped BigOperators NNReal
namespace AlternatingAnalytic.TruncatedPolynomial

/-- The algebra `L[ε]/(ε^n)`. -/
abbrev A (L : Type*) [Field L] (n : ℕ) :=
  AdjoinRoot (Polynomial.X ^ n : Polynomial L)

variable (L : Type*) (n : ℕ)

section Algebra

variable [Field L]

/-- The element `ε`, the class of `X`. -/
def epsilon : A L n := AdjoinRoot.root (Polynomial.X ^ n : Polynomial L)

/-- The basis `1, ε, …, ε^(n-1)`, indexed by `Fin n`. -/
def basis : Module.Basis (Fin n) L (A L n) :=
  (AdjoinRoot.powerBasis' (Polynomial.monic_X_pow n :
    (Polynomial.X ^ n : Polynomial L).Monic)).basis.reindex
      (finCongr (Polynomial.natDegree_X_pow n))

/-- Coefficients in the basis `1, ε, …, ε^(n-1)`. -/
def coeff : A L n ≃ₗ[L] (Fin n → L) := (basis L n).equivFun

instance instNontrivial [NeZero n] : Nontrivial (A L n) := by
  apply AdjoinRoot.nontrivial (Polynomial.X ^ n : Polynomial L)
  simpa [Polynomial.degree_X_pow] using
    (show (n : WithBot ℕ) ≠ 0 by exact_mod_cast NeZero.ne n)

theorem basis_eq_pow (i : Fin n) : basis L n i = epsilon L n ^ (i : ℕ) := by
  simp only [basis, Module.Basis.reindex_apply,
    (AdjoinRoot.powerBasis' (Polynomial.monic_X_pow n :
      (Polynomial.X ^ n : Polynomial L).Monic)).basis_eq_pow]
  rfl

@[simp] theorem epsilon_pow : epsilon L n ^ n = 0 := by
  have h := AdjoinRoot.eval₂_root (Polynomial.X ^ n : Polynomial L)
  simpa [epsilon] using h

theorem epsilon_pow_eq_zero {m : ℕ} (h : n ≤ m) : epsilon L n ^ m = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add, epsilon_pow, zero_mul]

@[simp] theorem coeff_basis (i j : Fin n) :
    coeff L n (basis L n i) j = if i = j then 1 else 0 := by
  exact (basis L n).equivFun_self i j

theorem coeff_pow (m : ℕ) (k : Fin n) :
    coeff L n (epsilon L n ^ m) k = if m = (k : ℕ) then 1 else 0 := by
  by_cases hm : m < n
  · rw [← basis_eq_pow L n ⟨m, hm⟩, coeff_basis]
    simp only [Fin.ext_iff]
  · rw [epsilon_pow_eq_zero L n (Nat.le_of_not_gt hm)]
    have hmk : m ≠ (k : ℕ) := by omega
    simp [hmk]

theorem expansion (x : A L n) : x = ∑ i : Fin n, coeff L n x i • basis L n i := by
  exact ((basis L n).sum_equivFun x).symm

/-- Multiplication is truncated convolution of coefficients. -/
theorem coeff_mul (x y : A L n) (k : Fin n) :
    coeff L n (x * y) k =
      ∑ i : Fin n, ∑ j : Fin n,
        if (i : ℕ) + (j : ℕ) = (k : ℕ) then coeff L n x i * coeff L n y j else 0 := by
  conv_lhs => rw [expansion L n x, expansion L n y]
  simp_rw [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm,
    basis_eq_pow, ← pow_add, map_sum, map_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, coeff_pow, mul_ite, mul_one, mul_zero]

end Algebra

section Norm

variable [NontriviallyNormedField L]

/-- The maximum norm on coefficients. -/
instance instNormedAddCommGroup : NormedAddCommGroup (A L n) :=
  NormedAddCommGroup.induced (A L n) (Fin n → L) (coeff L n) (coeff L n).injective

instance instNormedSpace : NormedSpace L (A L n) :=
  NormedSpace.induced L (A L n) (Fin n → L) (coeff L n)

/-- The coefficient map is a linear isometry onto `Fin n → L` with the sup norm. -/
def coefficientIsometry : A L n ≃ₗᵢ[L] (Fin n → L) :=
  { coeff L n with norm_map' := fun _ => rfl }

@[simp]
theorem coefficientIsometry_apply (x : A L n) :
    coefficientIsometry L n x = coeff L n x := rfl

theorem coefficientIsometry_symm_apply (v : Fin n → L) :
    (coefficientIsometry L n).symm v = ∑ i : Fin n, v i • epsilon L n ^ (i : ℕ) := by
  change (basis L n).equivFun.symm v = _
  rw [Module.Basis.equivFun_symm_apply]
  simp_rw [basis_eq_pow]

@[simp]
theorem norm_coeff (x : A L n) : ‖coeff L n x‖ = ‖x‖ := rfl

/-- The norm is the maximum of the coefficient norms. -/
theorem norm_eq_max (x : A L n) :
    ‖x‖ = (Finset.univ.sup fun i : Fin n => ‖coeff L n x i‖₊ : ℝ≥0) := rfl

theorem norm_coefficient_le (x : A L n) (i : Fin n) :
    ‖coeff L n x i‖ ≤ ‖x‖ := norm_le_pi_norm (coeff L n x) i

@[simp]
theorem norm_basis (i : Fin n) : ‖basis L n i‖ = 1 := by
  rw [← norm_coeff]
  have h : coeff L n (basis L n i) = Pi.single i 1 := by
    ext j
    simp [coeff_basis, Pi.single_apply, eq_comm]
  rw [h, Pi.norm_single, norm_one]

@[simp]
theorem norm_epsilon_pow (i : Fin n) : ‖epsilon L n ^ (i : ℕ)‖ = 1 := by
  rw [← basis_eq_pow, norm_basis]

instance instNormOneClass [NeZero n] : NormOneClass (A L n) where
  norm_one := by
    simpa using norm_epsilon_pow L n (⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ : Fin n)

instance instCompleteSpace [CompleteSpace L] : CompleteSpace (A L n) :=
  (coefficientIsometry L n).toIsometryEquiv.completeSpace

section Ultrametric

variable [IsUltrametricDist L]

instance instIsUltrametricDist : IsUltrametricDist (A L n) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y => by
    change ‖coeff L n (x + y)‖ ≤ max ‖coeff L n x‖ ‖coeff L n y‖
    rw [map_add]
    apply (pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg _))).2
    intro i
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le_max (norm_le_pi_norm _ i) (norm_le_pi_norm _ i))

/-- Over an ultrametric field the norm is submultiplicative. -/
theorem norm_mul_le (x y : A L n) : ‖x * y‖ ≤ ‖x‖ * ‖y‖ := by
  change ‖coeff L n (x * y)‖ ≤ ‖coeff L n x‖ * ‖coeff L n y‖
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
  intro k
  rw [coeff_mul]
  change ‖∑ i : Fin n, ∑ j : Fin n,
    if (i : ℕ) + (j : ℕ) = (k : ℕ) then coeff L n x i * coeff L n y j else 0‖₊ ≤
      ‖coeff L n x‖₊ * ‖coeff L n y‖₊
  apply (Finset.nnnorm_sum_le_sup_nnnorm _ _).trans
  apply Finset.sup_le
  intro i _
  apply (Finset.nnnorm_sum_le_sup_nnnorm _ _).trans
  apply Finset.sup_le
  intro j _
  split_ifs
  · rw [nnnorm_mul]
    exact mul_le_mul' (nnnorm_le_pi_nnnorm _ i) (nnnorm_le_pi_nnnorm _ j)
  · simp

instance instNormedCommRing : NormedCommRing (A L n) :=
  { instNormedAddCommGroup L n, (inferInstance : CommRing (A L n)) with
    norm_mul_le := norm_mul_le L n }

instance instNormedAlgebra : NormedAlgebra L (A L n) where
  norm_smul_le := (instNormedSpace L n).norm_smul_le

/-- Summary of the properties of the maximum norm on `L[ε]/(ε^n)`, for `n ≠ 0`. -/
theorem max_norm_properties [NeZero n] :
    (∀ x : A L n,
      ‖x‖ = (Finset.univ.sup fun i : Fin n => ‖coeff L n x i‖₊ : ℝ≥0)) ∧
      Isometry (coefficientIsometry L n) ∧
      (∀ x : A L n, coefficientIsometry L n x = coeff L n x) ∧
      (∀ v : Fin n → L,
        (coefficientIsometry L n).symm v = ∑ i : Fin n, v i • epsilon L n ^ (i : ℕ)) ∧
      (∀ (x y : A L n) (k : Fin n),
        coeff L n (x * y) k =
          ∑ i : Fin n, ∑ j : Fin n,
            if (i : ℕ) + (j : ℕ) = (k : ℕ) then coeff L n x i * coeff L n y j else 0) ∧
      (CompleteSpace L → CompleteSpace (A L n)) ∧
      epsilon L n ^ n = 0 ∧
      (∀ i : Fin n, basis L n i = epsilon L n ^ (i : ℕ)) ∧
      (∀ i : Fin n, ‖basis L n i‖ = 1) ∧
      (∀ i : Fin n, ‖epsilon L n ^ (i : ℕ)‖ = 1) ∧
      ‖(1 : A L n)‖ = 1 ∧
      (∀ x y : A L n, ‖x * y‖ ≤ ‖x‖ * ‖y‖) := by
  exact ⟨norm_eq_max L n, (coefficientIsometry L n).isometry,
    coefficientIsometry_apply L n, coefficientIsometry_symm_apply L n,
    coeff_mul L n, fun _ => instCompleteSpace L n, epsilon_pow L n,
    basis_eq_pow L n, norm_basis L n, norm_epsilon_pow L n, norm_one, norm_mul_le L n⟩

/-- The same summary for `n = p` prime, the case used in Appendix H. -/
theorem prime_max_norm_properties (p : ℕ) [Fact p.Prime] :
    (∀ x : A L p,
      ‖x‖ = (Finset.univ.sup fun i : Fin p => ‖coeff L p x i‖₊ : ℝ≥0)) ∧
      Isometry (coefficientIsometry L p) ∧
      (∀ x : A L p, coefficientIsometry L p x = coeff L p x) ∧
      (∀ v : Fin p → L,
        (coefficientIsometry L p).symm v = ∑ i : Fin p, v i • epsilon L p ^ (i : ℕ)) ∧
      (∀ (x y : A L p) (k : Fin p),
        coeff L p (x * y) k =
          ∑ i : Fin p, ∑ j : Fin p,
            if (i : ℕ) + (j : ℕ) = (k : ℕ) then coeff L p x i * coeff L p y j else 0) ∧
      (CompleteSpace L → CompleteSpace (A L p)) ∧
      epsilon L p ^ p = 0 ∧
      (∀ i : Fin p, basis L p i = epsilon L p ^ (i : ℕ)) ∧
      (∀ i : Fin p, ‖basis L p i‖ = 1) ∧
      (∀ i : Fin p, ‖epsilon L p ^ (i : ℕ)‖ = 1) ∧
      ‖(1 : A L p)‖ = 1 ∧
      (∀ x y : A L p, ‖x * y‖ ≤ ‖x‖ * ‖y‖) :=
  max_norm_properties L p

end Ultrametric
end Norm
end AlternatingAnalytic.TruncatedPolynomial
