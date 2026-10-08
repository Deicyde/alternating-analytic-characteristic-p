import Mathlib.Algebra.MvPolynomial.Funext
import AlternatingAnalytic.Algebra.PolynomialIdentity

/-!
# Lemma B.6 (identity principle), p. 28

Paper statement: "Let K be an infinite field, Y a K-vector space and
g(λ) = ∑_α λ^α y_α a polynomial in λ ∈ K^m with finitely many nonzero coefficients
y_α ∈ Y. If g(λ) = 0 for all λ ∈ K^m, then every y_α = 0."

Formalization notes:
* The coefficient family is a finitely supported map `y : (Fin m →₀ ℕ) →₀ Y` from
  multi-indices to `Y`; `λ^α` is `∏ i, λ i ^ α i`, and `g(λ)` is the finite sum over
  `y.support`. The variable is named `t` because `λ` is reserved syntax in Lean.
* `Y` need not be finite-dimensional, and no degree bound is imposed, as in the paper.
* No definitions are introduced.
-/

namespace AlternatingAnalyticChallenge.LemB_6

/-- **Lemma B.6.** A vector-valued polynomial vanishing on all of `K^m`, `K` infinite, has
all coefficients zero. -/
theorem identity_principle
    (K : Type*) [Field K] [Infinite K] (Y : Type*) [AddCommGroup Y] [Module K Y] (m : ℕ)
    (y : (Fin m →₀ ℕ) →₀ Y)
    (hg : ∀ t : Fin m → K, ∑ α ∈ y.support, (∏ i, t i ^ α i) • y α = 0) :
    ∀ α, y α = 0 := by
  exact VectorPolynomial.coeff_eq_zero_of_sum_eq_zero y hg

end AlternatingAnalyticChallenge.LemB_6
