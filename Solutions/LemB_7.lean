import Mathlib.RingTheory.MvPolynomial.Homogeneous
import AlternatingAnalytic.Algebra.FiniteHomogeneousIdentity

/-!
# Proof of Lemma B.7

Uses `AlternatingAnalytic.finiteField_homogeneous_extension_eq_zero`
(`AlternatingAnalytic/Algebra/FiniteHomogeneousIdentity.lean`).
-/

namespace AlternatingAnalyticChallenge.LemB_7

/-- A homogeneous form of degree `1 ≤ e ≤ q` over an extension of `F_q` that vanishes on
`F_q^m` is zero. -/
theorem finiteField_homogeneous_form_eq_zero
    (Fq : Type*) [Field Fq] [Fintype Fq] (L' : Type*) [Field L'] [Algebra Fq L'] (m e : ℕ)
    (he₁ : 1 ≤ e) (he : e ≤ Fintype.card Fq)
    (g : MvPolynomial (Fin m) L') (hg : g.IsHomogeneous e)
    (hvanish : ∀ t : Fin m → Fq, MvPolynomial.eval (fun i => algebraMap Fq L' (t i)) g = 0) :
    g = 0 := by
  exact AlternatingAnalytic.finiteField_homogeneous_extension_eq_zero g hg he hvanish

end AlternatingAnalyticChallenge.LemB_7
