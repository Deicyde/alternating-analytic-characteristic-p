import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Pi

/-! Polynomial coefficient comparison for rigid sources, over arbitrary fields.
The degree-two cancellation takes place in the polynomial ring. -/

noncomputable section
open scoped BigOperators
namespace AlternatingAnalytic.RigidDenseSource
open MvPolynomial

variable {K L I : Type*} [Field K] [Field L] [Algebra K L] [Fintype I]

private def linearPolynomial (c : I → K) : MvPolynomial I K :=
  ∑ j, C (c j) * X j

private theorem linearPolynomial_homogeneous (c : I → K) :
    (linearPolynomial c).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro j _
  exact (isHomogeneous_C I (c j)).mul (isHomogeneous_X K j)

private theorem linearPolynomial_coeff (c : I → K) (j : I) :
    (linearPolynomial c).coeff (Finsupp.single j 1) = c j := by
  classical
  simp [linearPolynomial, coeff_C_mul, coeff_X,
    Finsupp.single_eq_single_iff]

private theorem linearPolynomial_constant (c : I → K) :
    (linearPolynomial c).coeff 0 = 0 := by
  classical
  simp [linearPolynomial, coeff_C_mul, coeff_X]

private theorem linearPolynomial_aeval (c : I → K) (a : I → L) :
    aeval a (linearPolynomial c) = ∑ j, algebraMap K L (c j) * a j := by
  simp [linearPolynomial]

/-- Coefficient comparison for the polynomial relation forced by preservation of the source. -/
theorem polynomial_coordinate_rigidity [Nonempty I] [DecidableEq I] (a : I → L)
    (ha : AlgebraicIndependent K a) (M : I → I → K) (c b : I → K) (s : K)
    (h : ∀ i, (∑ j, algebraMap K L (M i j) * a j) +
      a i * (∑ j, algebraMap K L (c j) * a j) =
      algebraMap K L (b i) + algebraMap K L s * a i) :
    (∀ j, c j = 0) ∧ (∀ i, b i = 0) ∧
      (∀ i j, M i j = if i = j then s else 0) := by
  classical
  have hp (i : I) : linearPolynomial (M i) + X i * linearPolynomial c -
      C (b i) - C s * X i = (0 : MvPolynomial I K) := by
    apply ha.eq_zero_of_aeval_eq_zero
    simpa [linearPolynomial_aeval, sub_sub, sub_eq_zero] using h i
  have hc : linearPolynomial c = (0 : MvPolynomial I K) := by
    let i : I := Classical.choice inferInstance
    have h₂ := congrArg (homogeneousComponent 2) (hp i)
    have hquad : (X i * linearPolynomial c).IsHomogeneous 2 :=
      (isHomogeneous_X K i).mul (linearPolynomial_homogeneous c)
    have hlin : (C s * X i : MvPolynomial I K).IsHomogeneous 1 :=
      (isHomogeneous_C I s).mul (isHomogeneous_X K i)
    simp only [map_sub, map_add, map_zero,
      homogeneousComponent_of_mem (linearPolynomial_homogeneous (M i)),
      homogeneousComponent_of_mem hquad,
      homogeneousComponent_of_mem (isHomogeneous_C I (b i)),
      homogeneousComponent_of_mem hlin] at h₂
    norm_num at h₂
    exact h₂
  refine ⟨fun j => ?_, fun i => ?_, fun i j => ?_⟩
  · have := congrArg (fun p : MvPolynomial I K => p.coeff (Finsupp.single j 1)) hc
    simpa [linearPolynomial_coeff] using this
  · have := congrArg (fun p : MvPolynomial I K => p.coeff 0) (hp i)
    simpa [hc, linearPolynomial_constant, coeff_C_mul, coeff_X] using this
  · have := congrArg (fun p : MvPolynomial I K => p.coeff (Finsupp.single j 1)) (hp i)
    simp [hc, linearPolynomial_coeff, coeff_C_mul, coeff_X,
      Finsupp.single_eq_single_iff] at this
    have hz : (0 : I →₀ ℕ) ≠ Finsupp.single j 1 := by simp [eq_comm]
    simpa only [ite_eq_right hz, sub_zero, sub_eq_zero] using this

private theorem pi_apply_eq_sum_single {V : Type*} [AddCommGroup V] [Module L V]
    [DecidableEq I] (S : (I → L) →ₗ[L] V) (x : I → L) :
    S x = ∑ j, x j • S (Pi.single j 1) := by
  have hs (j : I) : (fun i : I => if j = i then (1 : L) else 0) = Pi.single j 1 := by
    funext i
    simp [Pi.single_apply, eq_comm]
  simpa only [hs] using S.pi_apply_eq_sum_univ x

/-- An ambient endomorphism with the prescribed source columns is scalar. -/
theorem ambient_endomorphism_eq_scalar [Nonempty I] [DecidableEq I]
    (a : I → L) (ha : AlgebraicIndependent K a)
    (S : (I → L) →ₗ[L] (I → L)) (M : I → I → K) (c b : I → K) (s : K)
    (hcol : ∀ i j, S (Pi.single j 1) i =
      algebraMap K L (M i j) + algebraMap K L (c j) * a i)
    (haS : ∀ i, S a i = algebraMap K L (b i) + algebraMap K L s * a i) :
    ∀ x, S x = algebraMap K L s • x := by
  have hrel (i : I) : (∑ j, algebraMap K L (M i j) * a j) +
      a i * (∑ j, algebraMap K L (c j) * a j) =
      algebraMap K L (b i) + algebraMap K L s * a i := by
    have hex := congrArg (fun v : I → L => v i) (pi_apply_eq_sum_single S a)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hcol] at hex
    rw [← haS i, hex, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  obtain ⟨hc, _, hM⟩ := polynomial_coordinate_rigidity a ha M c b s hrel
  intro x
  ext i
  have hex := congrArg (fun v : I → L => v i) (pi_apply_eq_sum_single S x)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hcol] at hex
  rw [hex]
  simp [hc, hM, apply_ite, mul_comm]

/-- A functional taking standard vectors and the independent tuple into the ground field vanishes. -/
theorem ambient_functional_eq_zero [DecidableEq I]
    (a : I → L) (ha : AlgebraicIndependent K a)
    (ell : (I → L) →ₗ[L] L) (c : I → K) (b : K)
    (hcol : ∀ j, ell (Pi.single j 1) = algebraMap K L (c j))
    (haell : ell a = algebraMap K L b) : ell = 0 := by
  have hp : linearPolynomial c - C b = (0 : MvPolynomial I K) := by
    apply ha.eq_zero_of_aeval_eq_zero
    simp only [map_sub, aeval_C, linearPolynomial_aeval, sub_eq_zero]
    rw [← haell, pi_apply_eq_sum_single ell a]
    simp only [hcol, smul_eq_mul, mul_comm]
  have hc (j : I) : c j = 0 := by
    have hcoeff := congrArg (fun p : MvPolynomial I K => p.coeff (Finsupp.single j 1)) hp
    have hz : (Finsupp.single j 1 : I →₀ ℕ) ≠ 0 := by simp
    simpa [linearPolynomial_coeff, coeff_C_of_ne_zero hz] using hcoeff
  apply LinearMap.ext
  intro x
  rw [pi_apply_eq_sum_single ell x]
  simp [hcol, hc]

end AlternatingAnalytic.RigidDenseSource
