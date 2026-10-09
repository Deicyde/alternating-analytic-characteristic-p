import Mathlib.Algebra.MvPolynomial.Funext
import AlternatingAnalytic.Algebra.PolynomialIdentity

/-!
# Proof of Lemma B.6

Uses `VectorPolynomial.coeff_eq_zero_of_sum_eq_zero`
(AlternatingAnalytic/Algebra/PolynomialIdentity.lean).
-/

namespace AlternatingAnalyticChallenge.LemB_6

/-- A vector-valued polynomial over an infinite field `K` that vanishes on all of `K^m` has
all coefficients zero. -/
theorem identity_principle
    (K : Type*) [Field K] [Infinite K] (Y : Type*) [AddCommGroup Y] [Module K Y] (m : ℕ)
    (y : (Fin m →₀ ℕ) →₀ Y)
    (hg : ∀ t : Fin m → K, ∑ α ∈ y.support, (∏ i, t i ^ α i) • y α = 0) :
    ∀ α, y α = 0 := by
  exact VectorPolynomial.coeff_eq_zero_of_sum_eq_zero y hg

end AlternatingAnalyticChallenge.LemB_6
