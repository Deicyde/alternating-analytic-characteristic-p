import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Lemma B.6 (identity principle), p. 31

Paper statement: "Let K be an infinite field, Y a K-vector space and
g(λ) = ∑_α λ^α y_α a polynomial in λ ∈ K^m with finitely many nonzero coefficients
y_α ∈ Y. If g(λ) = 0 for all λ ∈ K^m, then every y_α = 0."

## Formalization notes
* The coefficients are a finitely supported map `y : (Fin m →₀ ℕ) →₀ Y`; `λ^α` is
  `∏ i, λ i ^ α i`, and `g(λ)` is the sum over `y.support`.
* The variable is named `t` because `λ` is reserved in Lean.
-/

namespace AlternatingAnalyticChallenge.LemB_6

/-- A vector-valued polynomial over an infinite field `K` that vanishes on all of `K^m` has
all coefficients zero. -/
theorem identity_principle
    (K : Type*) [Field K] [Infinite K] (Y : Type*) [AddCommGroup Y] [Module K Y] (m : ℕ)
    (y : (Fin m →₀ ℕ) →₀ Y)
    (hg : ∀ t : Fin m → K, ∑ α ∈ y.support, (∏ i, t i ^ α i) • y α = 0) :
    ∀ α, y α = 0 := by
  sorry

end AlternatingAnalyticChallenge.LemB_6
