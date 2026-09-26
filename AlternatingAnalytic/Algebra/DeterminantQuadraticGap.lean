import AlternatingAnalytic.Algebra.DeterminantQuadraticReduction
import AlternatingAnalytic.Algebra.DeterminantQuadraticPhi
import AlternatingAnalytic.Analysis.DeterminantCoefficientSpaces
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Quadratic coefficient gap for the determinant source

The degree-one coefficient space vanishes in every prime characteristic, including two.
The algebraic theorem uses the literal determinant generators over an arbitrary field.
The final section identifies them definitionally with the coefficient spaces of the
actual t-adic determinant pair. Specialization is algebraic throughout.
-/

noncomputable section
open scoped BigOperators NNReal
open MvPolynomial
namespace AlternatingAnalytic.DeterminantQuadratic
variable (K : Type*) [Field K] (p : ℕ)

theorem homogeneous_linear_eq_sum {P : Poly K p} (hP : P.IsHomogeneous 1) :
    ∃ c : Fin p → K, P = ∑ j, c j • X j := by
  have h : P ∈ Submodule.span K (Set.range (X : Fin p → Poly K p)) := by
    rw [← homogeneousSubmodule_one_eq_span_X]
    exact hP
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp h
  exact ⟨c, hc.symm⟩

theorem coeff_shifted_sum (c : Fin p → K) (j : Fin p) :
    (∑ k : Fin p, c k • (Polynomial.X : Polynomial K) ^ (p - 1 + k.val)).coeff
      (p - 1 + j.val) = c j := by
  classical
  rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    have hbj : p - 1 + j.val ≠ p - 1 + b.val := by
      intro he
      exact hb (Fin.ext (by omega))
    simp only [Polynomial.coeff_smul, Polynomial.coeff_X_pow, ite_eq_right hbj, smul_zero]
  · simp

theorem coeff_sum_X_C (c : Fin p → K) (j : Fin p) :
    (∑ i : Fin p, (X i : Poly K p) * C (c i)).coeff (Finsupp.single j 1) = c j := by
  classical
  rw [coeff_sum]
  simp_rw [mul_comm (X _) (C _), coeff_C_mul, coeff_single_X]
  simp

variable [CharP K p] [Fact p.Prime]

/-- The concrete map `phi` kills the quadratic component of every determinant coefficient. -/
theorem phi_homogeneousComponent_two_eq_zero {P : Poly K p} (hP : P ∈ G0poly K p) :
    phi K p (homogeneousComponent 2 P) = 0 :=
  phi_eq_zero_of_mem_quadraticSpan K p (homogeneousComponent_two_mem_quadraticSpan K p hP)

/-- A homogeneous linear coefficient is detected by multiplication by the last variable. -/
theorem homogeneous_linear_eq_zero {P : Poly K p}
    (hP : P ∈ C0poly K p) (hlin : P.IsHomogeneous 1) : P = 0 := by
  classical
  obtain ⟨c, hc⟩ := homogeneous_linear_eq_sum K p hlin
  let top : Fin p := ⟨p - 1, by have := (Fact.out : p.Prime).pos; omega⟩
  have hquad : (X top * P).IsHomogeneous 2 := (isHomogeneous_X K top).mul hlin
  have hzero : phi K p (X top * P) = 0 := by
    have h := phi_homogeneousComponent_two_eq_zero K p ((mem_C0poly K p).mp hP |>.2 top)
    rwa [homogeneousComponent_eq_self hquad] at h
  have hphi : phi K p (X top * P) =
      ∑ j : Fin p, c j • (Polynomial.X : Polynomial K) ^ (p - 1 + j.val) := by
    rw [hc, Finset.mul_sum, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_smul_comm, map_smul, phi_X_mul_X]
    simp [top]
  have hc0 (j : Fin p) : c j = 0 := by
    have h := congrArg (fun Q : Polynomial K => Q.coeff (p - 1 + j.val)) hzero
    rw [hphi, coeff_shifted_sum] at h
    exact h
  simp [hc, hc0]

/-- The degree-one component of the actual algebraic coefficient submodule vanishes. -/
theorem homogeneousComponent_one_eq_zero {P : Poly K p} (hP : P ∈ C0poly K p) :
    homogeneousComponent 1 P = 0 :=
  homogeneous_linear_eq_zero K p (homogeneousComponent_mem_C0poly K p 1 hP)
    (homogeneousComponent_isHomogeneous 1 P)

/-- All conclusions of the quadratic coefficient-gap argument, with its concrete maps. -/
theorem quadratic_coefficient_gap :
    (∀ n P, P ∈ G0poly K p → homogeneousComponent n P ∈ G0poly K p) ∧
    (∀ n P, P ∈ C0poly K p → homogeneousComponent n P ∈ C0poly K p) ∧
    (∀ P, P ∈ G0poly K p → homogeneousComponent 2 P ∈ quadraticSpan K p) ∧
    (∀ i j, phi K p (X i * X j) =
      if p - 1 ≤ i.val + j.val then (Polynomial.X : Polynomial K) ^ (i.val + j.val)
      else 0) ∧
    (∀ r s i j, phi K p (minor K p r s i j) = 0) ∧
    (∀ r, phi K p (squareCoordinate K p r) = 0) ∧
    (∀ P, P ∈ G0poly K p → phi K p (homogeneousComponent 2 P) = 0) ∧
    (∀ P, P ∈ C0poly K p → P.IsHomogeneous 1 → P = 0) ∧
    (∀ P, P ∈ C0poly K p → homogeneousComponent 1 P = 0) :=
  ⟨fun n _ h => homogeneousComponent_mem_G0poly K p n h,
    fun n _ h => homogeneousComponent_mem_C0poly K p n h,
    fun _ h => homogeneousComponent_two_mem_quadraticSpan K p h,
    phi_X_mul_X K p, phi_minor K p, phi_squareCoordinate K p,
    fun _ h => phi_homogeneousComponent_two_eq_zero K p h,
    fun _ h => homogeneous_linear_eq_zero K p h,
    fun _ h => homogeneousComponent_one_eq_zero K p h⟩

/-- The constant-component contradiction; no coefficient `d i` is assumed homogeneous. -/
theorem no_coefficient_family :
    ¬ ∃ d : Fin p → C0poly K p, (d 0 : Poly K p) = 1 ∧
      (∑ i : Fin p, X i * (d i : Poly K p)) ∈ C0poly K p := by
  classical
  rintro ⟨d, hd0, hsum⟩
  have hzero := homogeneousComponent_one_eq_zero K p hsum
  have hcomponent : homogeneousComponent 1 (∑ i : Fin p, X i * (d i : Poly K p)) =
      ∑ i : Fin p, X i * C ((d i : Poly K p).coeff 0) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [show 1 = 0 + 1 from rfl, homogeneousComponent_X_mul, homogeneousComponent_zero]
  have hcoeff := congrArg (fun Q : Poly K p => Q.coeff (Finsupp.single (0 : Fin p) 1)) hzero
  rw [hcomponent, coeff_sum_X_C, hd0] at hcoeff
  simp at hcoeff

end AlternatingAnalytic.DeterminantQuadratic

namespace AlternatingAnalytic.DeterminantPair

variable (p : ℕ) [Fact p.Prime] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)]

local instance gapNormedFieldK : NormedField (K p r) :=
  (inferInstance : NontriviallyNormedField (K p r)).toNormedField
local instance gapFieldK : Field (K p r) :=
  (inferInstance : NontriviallyNormedField (K p r)).toField

/-- The generic algebraic model is literally the previously defined determinant span. -/
theorem G0poly_eq_algebraic : G0poly p r = DeterminantQuadratic.G0poly (K p r) p := rfl

/-- The generic coefficient membership conditions are literally the previous conditions. -/
theorem C0poly_eq_algebraic : C0poly p r = DeterminantQuadratic.C0poly (K p r) p := rfl

theorem homogeneousComponent_mem_G0poly (n : ℕ) {P : Poly0 p r} (hP : P ∈ G0poly p r) :
    homogeneousComponent n P ∈ G0poly p r :=
  DeterminantQuadratic.homogeneousComponent_mem_G0poly (K p r) p n hP

theorem homogeneousComponent_mem_C0poly (n : ℕ) {P : Poly0 p r} (hP : P ∈ C0poly p r) :
    homogeneousComponent n P ∈ C0poly p r :=
  DeterminantQuadratic.homogeneousComponent_mem_C0poly (K p r) p n hP

/-- `dom:degree-gap` on the coefficient space from algebraic specialization. -/
theorem homogeneousComponent_one_eq_zero {P : Poly0 p r} (hP : P ∈ C0poly p r) :
    homogeneousComponent 1 P = 0 :=
  DeterminantQuadratic.homogeneousComponent_one_eq_zero (K p r) p hP

/-- The complete `dom:degree-gap` package for the original polynomial coefficient spaces. -/
theorem quadratic_coefficient_gap :
    (∀ n P, P ∈ G0poly p r → homogeneousComponent n P ∈ G0poly p r) ∧
    (∀ n P, P ∈ C0poly p r → homogeneousComponent n P ∈ C0poly p r) ∧
    (∀ P, P ∈ G0poly p r →
      homogeneousComponent 2 P ∈ DeterminantQuadratic.quadraticSpan (K p r) p) ∧
    (∀ i j, DeterminantQuadratic.phi (K p r) p (X i * X j) =
      if p - 1 ≤ i.val + j.val then
        (Polynomial.X : Polynomial (K p r)) ^ (i.val + j.val) else 0) ∧
    (∀ a b i j, DeterminantQuadratic.phi (K p r) p
      (DeterminantQuadratic.minor (K p r) p a b i j) = 0) ∧
    (∀ i, DeterminantQuadratic.phi (K p r) p
      (DeterminantQuadratic.squareCoordinate (K p r) p i) = 0) ∧
    (∀ P, P ∈ G0poly p r →
      DeterminantQuadratic.phi (K p r) p (homogeneousComponent 2 P) = 0) ∧
    (∀ P, P ∈ C0poly p r → P.IsHomogeneous 1 → P = 0) ∧
    (∀ P, P ∈ C0poly p r → homogeneousComponent 1 P = 0) :=
  DeterminantQuadratic.quadratic_coefficient_gap (K p r) p

/-- The exact constant-component obstruction used for the nonanalytic coordinate. -/
theorem no_coefficient_family :
    ¬ ∃ d : Fin p → C0poly p r, (d 0 : Poly0 p r) = 1 ∧
      (∑ i : Fin p, X i * (d i : Poly0 p r)) ∈ C0poly p r :=
  DeterminantQuadratic.no_coefficient_family (K p r) p

end AlternatingAnalytic.DeterminantPair
