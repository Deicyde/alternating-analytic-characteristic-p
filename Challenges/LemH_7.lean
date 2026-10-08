import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.Finite.Basic
import AlternatingAnalytic.Algebra.DeterminantQuadraticGap

/-!
# Lemma H.7 (the degree-one part of `C_0` is zero), p. 59

Setting (Appendix H.1–H.2): `p` is prime, `K = 𝔽_p(t)`, `A = L[ε]/(ε^p)` with basis
`e_i = ε^i`, `a = ∑ a_i e_i` with `a_0, …, a_{p-1}` (and the `τ_w`) algebraically independent over
`K`, and `D_0 = span_K{e_i, ε^i a : 0 ≤ i < p} + K a²`. Determinants are taken in the basis
`(e_0, …, e_{p-1})`. By algebraic independence, scalars that are polynomials in the `a_i` are
identified with elements of `K[a_0, …, a_{p-1}]`. "Algebraically set every `τ_w` to zero. The image
of `G` is `G_0 = span_K{det(d_1, …, d_p) : d_i ∈ D_0}`. Put
`C_0 = {λ ∈ G_0 : a_i λ ∈ G_0 for every i}`. … The displayed generators of `D_0` are homogeneous
polynomial vectors of degrees zero, one, and two. Their determinants are homogeneous, so `G_0` is
graded, and the defining conditions show that `C_0` is graded as well."

Paper statement: "The homogeneous degree-one part of `C_0` is zero."

Formalization notes:
* The import of `AlternatingAnalytic.Algebra.DeterminantQuadraticGap` (the library module that
  proves this lemma) is present only so that the challenge and the solution elaborate in the same
  environment: without it, Lean resolves the `Module` instance on the submodules `G0`, `C0`
  through `AddMonoidAlgebra.instModule` instead of `MvPolynomial.instModule`, and the two
  statements, though textually identical, print differently under `pp.all`. No definition or
  statement below depends on that module.
* Everything is algebraic, in the polynomial model the paper uses: the `a_i` are the variables
  `X 0, …, X (p-1)` of `MvPolynomial (Fin p) K`, and `K = 𝔽_p(t)` is Mathlib's
  `RatFunc (ZMod p)` (no norm is involved). `p` prime is `[Fact p.Prime]`.
* `generatorVector K p` (defined here) lists the coordinate vectors, in the basis `e_i`, of the
  displayed generators of `D_0`: `e_i` (the unit vector), `ε^i a` (coordinate `k` is
  `a_{k-i}` for `k ≥ i`, else `0`) and `a²` (coordinate `k` is `∑_{i+j=k} a_i a_j`, from
  `ε^p = 0`). `G0 K p` (defined here) is the `K`-span of the determinants of `p`-tuples of these
  generators (column `j` of the matrix is the `j`-th vector of the tuple). By multilinearity of
  the determinant this is the span of `det(d_1, …, d_p)` over all `d_i ∈ D_0`, as the paper
  itself notes for `G`; the generator form is used as the definition. `C0 K p` (defined here) is
  `{λ ∈ G_0 : a_i λ ∈ G_0 for every i}`.
* `part1` is the lemma: an element of `C_0` that is homogeneous of degree one is zero.
  `part2` is the form in which the lemma is used in H.3 of the paper, combining it with the
  gradedness of `C_0` asserted just before the lemma: the degree-one homogeneous component of
  every element of `C_0` is zero.
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
  sorry

/-- **Lemma H.7, with the gradedness of `C_0`.** The degree-one homogeneous component of every
element of `C_0` is zero. -/
theorem part2 (p : ℕ) [Fact p.Prime] (P : MvPolynomial (Fin p) (RatFunc (ZMod p)))
    (hP : P ∈ C0 (RatFunc (ZMod p)) p) : MvPolynomial.homogeneousComponent 1 P = 0 := by
  sorry

end AlternatingAnalyticChallenge.LemH_7
