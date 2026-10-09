import AlternatingAnalytic.Analysis.DeterminantCoefficientSpan
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# The multiplication family `x ↦ M_x`

For `x ∈ E`, multiplication by `x` in `A` restricts to a bounded map `M_x : E → D`, and
`x ↦ M_x` is a bounded linear family of norm at most one. The matrix of `M_x` is lower
triangular with diagonal `x_0`, so `det M_x = x_0^p`. These facts are used in the
nonanalytic cross-action of Theorem H.4.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators NNReal

namespace AlternatingAnalytic.DeterminantPair

variable (p : ℕ) [Fact p.Prime] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)]
attribute [local instance] preferredNormedFieldK preferredFieldK preferredFieldL

private theorem e_mul_e_mem_D (i j : Fin p) : e p r i * e p r j ∈ D p r := by
  rw [e_eq_epsilon_pow, e_eq_epsilon_pow, ← pow_add]
  by_cases h : (i : ℕ) + j < p
  · exact (e_eq_epsilon_pow p r ⟨i + j, h⟩) ▸ e_mem_D p r ⟨i + j, h⟩
  · rw [TruncatedPolynomial.epsilon_pow_eq_zero _ _ (Nat.le_of_not_gt h)]
    exact (D p r).zero_mem

private theorem sourceGen_mul_mem_D (i j : Fin p ⊕ Unit) :
    sourceGen p r i * sourceGen p r j ∈ D p r := by
  rcases i with i | u <;> rcases j with j | v
  · exact e_mul_e_mem_D p r i j
  · exact gen_mem_D p r (Sum.inr (Sum.inl i))
  · simpa [sourceGen, gen, mul_comm] using gen_mem_D p r (Sum.inr (Sum.inl j))
  · exact gen_mem_D p r (Sum.inr (Sum.inr (Sum.inl ())))

/-- The product of two elements of `E` lies in `D`. -/
theorem mul_mem_D (x y : E p r) : (x : A p r) * (y : A p r) ∈ D p r := by
  have hx : (x : A p r) ∈ Submodule.span (K p r) (Set.range (sourceGen p r)) := by
    rw [← E_eq_span_sourceGen]; exact x.property
  have hy : (y : A p r) ∈ Submodule.span (K p r) (Set.range (sourceGen p r)) := by
    rw [← E_eq_span_sourceGen]; exact y.property
  generalize (x : A p r) = xv at hx ⊢
  generalize (y : A p r) = yv at hy ⊢
  induction hx using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      induction hy using Submodule.span_induction with
      | mem z hz =>
          obtain ⟨j, rfl⟩ := hz
          exact sourceGen_mul_mem_D p r i j
      | zero => simp
      | add z w hz hw iz iw => simpa [mul_add] using (D p r).add_mem iz iw
      | smul s z hz iz => simpa [mul_smul_comm] using (D p r).smul_mem s iz
  | zero => simp
  | add z w hz hw iz iw => simpa [add_mul] using (D p r).add_mem iz iw
  | smul s z hz iz => simpa [smul_mul_assoc] using (D p r).smul_mem s iz

/-- Multiplication by `x`, as a bounded map `E → D`. -/
def multiplicationAt (x : E p r) : E p r →L[K p r] D p r :=
  (((ContinuousLinearMap.mul (K p r) (A p r)) (x : A p r)).comp
    (E p r).subtypeL).codRestrict (D p r) (mul_mem_D p r x)

@[simp] theorem multiplicationAt_apply (x y : E p r) :
    (multiplicationAt p r x y : A p r) = (x : A p r) * (y : A p r) := rfl

theorem norm_multiplicationAt_le (x : E p r) : ‖multiplicationAt p r x‖ ≤ ‖x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg x)
  intro y
  exact TruncatedPolynomial.norm_mul_le (L p r) p x y

/-- The bounded linear family `x ↦ M_x`. -/
def multiplication : E p r →L[K p r] E p r →L[K p r] D p r :=
  ({ toFun := multiplicationAt p r
     map_add' := fun x y => by ext z; simp [add_mul]
     map_smul' := fun s x => by ext z; simp } :
    E p r →ₗ[K p r] E p r →L[K p r] D p r).mkContinuous 1
      (fun x => by simpa using norm_multiplicationAt_le p r x)

@[simp] theorem multiplication_apply (x y : E p r) :
    (multiplication p r x y : A p r) = (x : A p r) * (y : A p r) := rfl

theorem norm_multiplication_apply_le (x : E p r) : ‖multiplication p r x‖ ≤ ‖x‖ :=
  norm_multiplicationAt_le p r x

/-- Multiplication by `x` on `A`, as an `L`-linear map. -/
def completedMultiplication (x : A p r) : A p r →L[L p r] A p r :=
  ContinuousLinearMap.mul (L p r) (A p r) x

@[simp] theorem completedMultiplication_apply (x y : A p r) :
    completedMultiplication p r x y = x * y := rfl

@[simp] theorem completedMultiplication_apply_source (x y : E p r) :
    completedMultiplication p r (x : A p r) (y : A p r) =
      (multiplication p r x y : A p r) := rfl

/-- The matrix of multiplication by `x` in the basis `e_i = ε^i`. -/
def multiplicationMatrix (x : A p r) : Matrix (Fin p) (Fin p) (L p r) :=
  fun i j => TruncatedPolynomial.coeff (L p r) p
    (completedMultiplication p r x (e p r j)) i

theorem multiplicationMatrix_apply (x : A p r) (i j : Fin p) :
    multiplicationMatrix p r x i j =
      ∑ k : Fin p, if (k : ℕ) + j = (i : ℕ)
        then TruncatedPolynomial.coeff (L p r) p x k else 0 := by
  unfold multiplicationMatrix
  simp only [completedMultiplication_apply]
  rw [TruncatedPolynomial.coeff_mul]
  apply Finset.sum_congr rfl
  intro k _
  simp only [e, TruncatedPolynomial.coeff_basis]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

/-- The multiplication matrix is lower triangular. -/
theorem multiplicationMatrix_isLowerTriangular (x : A p r) :
    (multiplicationMatrix p r x).IsLowerTriangular := by
  intro i j hij
  rw [multiplicationMatrix_apply]
  apply Finset.sum_eq_zero
  intro k _
  have h : ¬ (k : ℕ) + j = (i : ℕ) := by
    have hij' : i < j := hij
    omega
  simp [h]

@[simp] theorem multiplicationMatrix_diag (x : A p r) (i : Fin p) :
    multiplicationMatrix p r x i i = TruncatedPolynomial.coeff (L p r) p x 0 := by
  rw [multiplicationMatrix_apply, Finset.sum_eq_single 0]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

/-- The multiplication matrix has determinant `x_0^p`. -/
theorem det_multiplicationMatrix (x : A p r) :
    (multiplicationMatrix p r x).det =
      TruncatedPolynomial.coeff (L p r) p x 0 ^ p := by
  rw [Matrix.det_of_isLowerTriangular _ (multiplicationMatrix_isLowerTriangular p r x)]
  simp

/-- `det (x e_0, ..., x e_{p-1}) = x_0^p`. -/
theorem delta_mul_e (x : A p r) :
    delta p r (fun i => x * e p r i) = TruncatedPolynomial.coeff (L p r) p x 0 ^ p :=
  det_multiplicationMatrix p r x

end AlternatingAnalytic.DeterminantPair
