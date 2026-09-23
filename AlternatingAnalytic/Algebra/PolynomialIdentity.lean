import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Vector-valued polynomial identity principle

A finitely supported family of vector coefficients is zero if its polynomial
evaluation vanishes everywhere over an infinite field. Applying an arbitrary
algebraic linear functional reduces the assertion to `MvPolynomial.funext`;
algebraic dual functionals separate points in an arbitrary vector space.
-/

namespace VectorPolynomial

variable {K Y σ : Type*} [Field K] [AddCommGroup Y] [Module K Y]

/-- Evaluate finitely many vector-valued coefficients. Every multi-index is also
finitely supported, so both the outer sum and each monomial product are finite. -/
noncomputable def eval (c : (σ →₀ ℕ) →₀ Y) (x : σ → K) : Y :=
  c.sum fun α y => (α.prod fun i n => x i ^ n) • y

/-- Apply an algebraic functional to each coefficient to obtain an ordinary scalar
multivariate polynomial. -/
noncomputable def scalarPolynomial (φ : Y →ₗ[K] K) (c : (σ →₀ ℕ) →₀ Y) :
    MvPolynomial σ K :=
  AddMonoidAlgebra.ofCoeff (Finsupp.mapRange φ φ.map_zero c)

@[simp]
theorem scalarPolynomial_coeff (φ : Y →ₗ[K] K) (c : (σ →₀ ℕ) →₀ Y)
    (α : σ →₀ ℕ) : (scalarPolynomial φ c).coeff α = φ (c α) := rfl

/-- Scalar evaluation commutes with applying a linear functional to the coefficients. -/
theorem eval_scalarPolynomial (φ : Y →ₗ[K] K) (c : (σ →₀ ℕ) →₀ Y)
    (x : σ → K) : MvPolynomial.eval x (scalarPolynomial φ c) = φ (eval c x) := by
  classical
  change (Finsupp.mapRange φ φ.map_zero c).sum
      (fun α a => a * α.prod (fun i n => x i ^ n)) =
    φ (c.sum fun α y => (α.prod fun i n => x i ^ n) • y)
  rw [Finsupp.sum_mapRange_index (fun _ => zero_mul _)]
  simp only [Finsupp.sum, map_sum, map_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- For a finite variable type this is exactly the usual finite polynomial sum. -/
theorem eval_eq_sum [Fintype σ] (c : (σ →₀ ℕ) →₀ Y) (x : σ → K) :
    eval c x = ∑ α ∈ c.support, (∏ i, x i ^ α i) • c α := by
  simp only [eval, Finsupp.sum, Finsupp.prod_pow]

/-- Over an infinite field, vanishing polynomial evaluations force every vector
coefficient to vanish. The coefficient module need not be finite dimensional. -/
theorem coeff_eq_zero_of_eval_eq_zero [Infinite K] (c : (σ →₀ ℕ) →₀ Y)
    (h : ∀ x : σ → K, eval c x = 0) (α : σ →₀ ℕ) : c α = 0 := by
  apply (Module.forall_dual_apply_eq_zero_iff K (c α)).mp
  intro φ
  have hp : scalarPolynomial φ c = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [eval_scalarPolynomial, h x, map_zero, map_zero]
  have hc := congrArg (fun p : MvPolynomial σ K => p.coeff α) hp
  simpa only [scalarPolynomial_coeff, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using hc

/-- Equality to the zero finitely supported coefficient family. -/
theorem eq_zero_of_eval_eq_zero [Infinite K] (c : (σ →₀ ℕ) →₀ Y)
    (h : ∀ x : σ → K, eval c x = 0) : c = 0 := by
  ext α
  exact coeff_eq_zero_of_eval_eq_zero c h α

/-- The identity principle in the finite-variable, ordinary-monomial-sum notation
of the paper. No bound on the degrees is required. -/
theorem coeff_eq_zero_of_sum_eq_zero [Fintype σ] [Infinite K]
    (c : (σ →₀ ℕ) →₀ Y)
    (h : ∀ x : σ → K, ∑ α ∈ c.support, (∏ i, x i ^ α i) • c α = 0)
    (α : σ →₀ ℕ) : c α = 0 := by
  apply coeff_eq_zero_of_eval_eq_zero (K := K) c _ α
  intro x
  rw [eval_eq_sum]
  exact h x

end VectorPolynomial
