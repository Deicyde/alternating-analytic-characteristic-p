import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Lemma B.7 (homogeneous forms over a finite field), p. 29

Paper statement: "Let q be a prime power, L′ ⊇ F_q a field, 1 ≤ e ≤ q, and
g ∈ L′[λ₁, …, λ_m] homogeneous of degree e with g(λ) = 0 for every λ ∈ F_q^m. Then g = 0."

Formalization notes:
* `F_q` is an arbitrary finite field `Fq` and `q` is `Fintype.card Fq` (automatically a
  prime power); `L′ ⊇ F_q` is a field `L'` with `[Algebra Fq L']`, and points of `F_q^m` are
  evaluated through `algebraMap Fq L'`.
* `g : MvPolynomial (Fin m) L'` with `g.IsHomogeneous e`.
* The hypothesis `1 ≤ e` is kept as in the paper.
* No definitions are introduced.
-/

namespace AlternatingAnalyticChallenge.LemB_7

/-- **Lemma B.7.** A homogeneous form of degree `1 ≤ e ≤ q` over an extension of `F_q`
that vanishes on `F_q^m` is zero. -/
theorem finiteField_homogeneous_form_eq_zero
    (Fq : Type*) [Field Fq] [Fintype Fq] (L' : Type*) [Field L'] [Algebra Fq L'] (m e : ℕ)
    (he₁ : 1 ≤ e) (he : e ≤ Fintype.card Fq)
    (g : MvPolynomial (Fin m) L') (hg : g.IsHomogeneous e)
    (hvanish : ∀ t : Fin m → Fq, MvPolynomial.eval (fun i => algebraMap Fq L' (t i)) g = 0) :
    g = 0 := by
  sorry

end AlternatingAnalyticChallenge.LemB_7
