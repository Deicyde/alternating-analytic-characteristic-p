import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.Finite.Basic
import AlternatingAnalytic.Algebra.DeterminantQuadraticGap

/-!
# Lemma H.7 (the degree-one part of `C_0` is zero), p. 60

Solution: the statements of `Challenges/LemH_7.lean`, from
`AlternatingAnalytic.DeterminantQuadratic.homogeneous_linear_eq_zero` and
`AlternatingAnalytic.DeterminantQuadratic.homogeneousComponent_one_eq_zero`
(`AlternatingAnalytic/Algebra/DeterminantQuadraticGap.lean`, collected in
`DeterminantQuadratic.quadratic_coefficient_gap`), proved for every field of prime
characteristic `p`; here the field is `RatFunc (ZMod p)`. The file's `generatorVector`,
`generatorDet`, `G0` and `C0` are the library's `genPoly`, `detPoly`, `G0poly` and `C0poly`
(`AlternatingAnalytic/Algebra/DeterminantQuadraticBasic.lean`) verbatim.
-/

namespace AlternatingAnalyticChallenge.LemH_7

open scoped BigOperators

section Definitions

variable (K : Type*) [Field K] (p : ℕ)

/-- Coordinate vectors, in the basis `e_0, …, e_{p-1}`, of the generators of `D_0`:
`Sum.inl i ↦ e_i`, `Sum.inr (Sum.inl i) ↦ ε^i a`, `Sum.inr (Sum.inr ()) ↦ a²`, with the
`a_j` replaced by the variables `X j`. -/
noncomputable def generatorVector : Fin p ⊕ (Fin p ⊕ Unit) → Fin p → MvPolynomial (Fin p) K
  | Sum.inl i => fun k => if i = k then 1 else 0
  | Sum.inr (Sum.inl i) => fun k =>
      ∑ j : Fin p, if (i : ℕ) + (j : ℕ) = (k : ℕ) then MvPolynomial.X j else 0
  | Sum.inr (Sum.inr _) => fun k =>
      ∑ i : Fin p, ∑ j : Fin p, if (i : ℕ) + (j : ℕ) = (k : ℕ)
        then MvPolynomial.X i * MvPolynomial.X j else 0

/-- The determinant of a `p`-tuple of generators of `D_0`, the `j`-th generator being the
`j`-th column. -/
noncomputable def generatorDet (s : Fin p → Fin p ⊕ (Fin p ⊕ Unit)) : MvPolynomial (Fin p) K :=
  Matrix.det (Matrix.of (fun i j => generatorVector K p (s j) i))

/-- `G_0 = span_K {det(d_1, …, d_p) : d_i ∈ D_0}`, in the polynomial model. -/
noncomputable def G0 : Submodule K (MvPolynomial (Fin p) K) :=
  Submodule.span K (Set.range (generatorDet K p))

/-- `C_0 = {λ ∈ G_0 : a_i λ ∈ G_0 for every i}`. -/
noncomputable def C0 : Submodule K (MvPolynomial (Fin p) K) :=
  G0 K p ⊓ ⨅ i : Fin p, (G0 K p).comap (LinearMap.mulLeft K (MvPolynomial.X i))

end Definitions

/-- **Lemma H.7.** The homogeneous degree-one part of `C_0` is zero: every element of `C_0`
that is homogeneous of degree one vanishes. -/
theorem part1 (p : ℕ) [Fact p.Prime] (P : MvPolynomial (Fin p) (RatFunc (ZMod p)))
    (hP : P ∈ C0 (RatFunc (ZMod p)) p) (hlin : P.IsHomogeneous 1) : P = 0 := by
  exact AlternatingAnalytic.DeterminantQuadratic.homogeneous_linear_eq_zero
    (RatFunc (ZMod p)) p hP hlin

/-- **Lemma H.7, with the gradedness of `C_0`.** The degree-one homogeneous component of every
element of `C_0` is zero. -/
theorem part2 (p : ℕ) [Fact p.Prime] (P : MvPolynomial (Fin p) (RatFunc (ZMod p)))
    (hP : P ∈ C0 (RatFunc (ZMod p)) p) : MvPolynomial.homogeneousComponent 1 P = 0 := by
  exact AlternatingAnalytic.DeterminantQuadratic.homogeneousComponent_one_eq_zero
    (RatFunc (ZMod p)) p hP

end AlternatingAnalyticChallenge.LemH_7
