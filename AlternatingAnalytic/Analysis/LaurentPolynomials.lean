import AlternatingAnalytic.Analysis.LaurentField
import Mathlib.Algebra.Polynomial.Laurent

/-! The coefficient-preserving Laurent-polynomial inclusion into Laurent series. -/

noncomputable section

open scoped NNReal

namespace AlternatingAnalytic

variable (κ : Type*) [Field κ]

/-- The monomial homomorphism used to include Laurent polynomials. -/
def laurentMonomialHom : Multiplicative ℤ →* LaurentSeries κ where
  toFun n := HahnSeries.single n.toAdd 1
  map_one' := rfl
  map_mul' a b := by
    change HahnSeries.single (a.toAdd + b.toAdd) (1 : κ) =
      HahnSeries.single a.toAdd 1 * HahnSeries.single b.toAdd 1
    rw [HahnSeries.single_mul_single, one_mul]

/-- The coefficient-preserving inclusion of Laurent polynomials into Laurent series. -/
def laurentPolynomialMap : LaurentPolynomial κ →ₐ[κ] LaurentSeries κ :=
  AddMonoidAlgebra.lift κ (LaurentSeries κ) ℤ (laurentMonomialHom κ)

@[simp]
theorem laurentPolynomialMap_single (n : ℤ) (c : κ) :
    laurentPolynomialMap κ (AddMonoidAlgebra.single n c) = HahnSeries.single n c := by
  rw [laurentPolynomialMap, AddMonoidAlgebra.lift_single, Algebra.smul_def]
  change (algebraMap κ (LaurentSeries κ) c) * HahnSeries.single n 1 = HahnSeries.single n c
  rw [LaurentSeries.algebraMap_apply, HahnSeries.C_apply, HahnSeries.single_mul_single]
  simp

@[simp]
theorem laurentPolynomialMap_coeff (p : LaurentPolynomial κ) (n : ℤ) :
    (laurentPolynomialMap κ p).coeff n = p.coeff n := by
  induction p using AddMonoidAlgebra.induction_on with
  | of a =>
    change (laurentPolynomialMap κ (AddMonoidAlgebra.single a 1)).coeff n =
      (AddMonoidAlgebra.single a (1 : κ)).coeff n
    rw [laurentPolynomialMap_single]
    simp [HahnSeries.coeff_single, eq_comm]
  | add a b ha hb =>
    rw [map_add, HahnSeries.coeff_add, ha, hb]
    rfl
  | smul c a ha =>
    change (laurentPolynomialMap κ (c • a)).coeff n = c * a.coeff n
    have hs : laurentPolynomialMap κ (c • a) =
        algebraMap κ (LaurentSeries κ) c * laurentPolynomialMap κ a := by
      rw [Algebra.smul_def, map_mul, AlgHom.commutes]
    rw [hs, LaurentSeries.algebraMap_apply, HahnSeries.C_apply,
      HahnSeries.coeff_single_zero_mul, ha]

theorem laurentPolynomialMap_injective : Function.Injective (laurentPolynomialMap κ) := by
  intro p q h
  apply LaurentPolynomial.ext
  intro n
  simpa only [laurentPolynomialMap_coeff] using congrArg (fun x : LaurentSeries κ => x.coeff n) h

end AlternatingAnalytic
