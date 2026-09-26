import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.RingTheory.AlgebraicIndependent.Defs

open scoped BigOperators

namespace AlternatingAnalytic

open MvPolynomial

/-- A column family whose distinguished variable occurs only in one distinguished
column has determinants of degree at most one in that variable. Repetition of
that column is handled by alternation, in every characteristic. -/
theorem degreeOf_det_column_family_le_one
    {K n J σ : Type*} [Field K] [Fintype n] [DecidableEq n] [DecidableEq J]
    (g : J → n → MvPolynomial σ K) (j₀ : J) (v : σ)
    (hdeg : ∀ j i, degreeOf v (g j i) ≤ if j = j₀ then 1 else 0)
    (s : n → J) :
    degreeOf v (Matrix.det (Matrix.of (fun i k => g (s k) i))) ≤ 1 := by
  classical
  by_cases hrep : ∃ i j, i ≠ j ∧ s i = j₀ ∧ s j = j₀
  · obtain ⟨i, j, hij, hi, hj⟩ := hrep
    rw [Matrix.det_zero_of_column_eq (M := Matrix.of (fun i k => g (s k) i)) hij
      (by intro k; simp [hi, hj])]
    simp
  · have hsum : (∑ k : n, if s k = j₀ then 1 else 0) ≤ 1 := by
      by_cases hex : ∃ k, s k = j₀
      · obtain ⟨k, hk⟩ := hex
        rw [Finset.sum_eq_single k]
        · simp [hk]
        · intro b _ hbk
          have hb : s b ≠ j₀ := fun hb => hrep ⟨b, k, hbk, hb, hk⟩
          simp [hb]
        · simp
      · simp only [not_exists] at hex
        simp [hex]
    rw [Matrix.det_apply']
    refine (degreeOf_sum_le v _ _).trans ?_
    refine Finset.sup_le ?_
    intro π _
    have hsign := degreeOf_C_mul_le (∏ k, g (s k) (π k)) v
      (((Equiv.Perm.sign π : ℤ) : K))
    have hprod := degreeOf_prod_le v Finset.univ (fun k => g (s k) (π k))
    apply le_trans (show degreeOf v _ ≤ degreeOf v (∏ k, g (s k) (π k)) by
      simpa using hsign)
    exact hprod.trans ((Finset.sum_le_sum
      (fun k _ => hdeg (s k) (π k))).trans hsum)

/-- The same individual-variable degree bound holds on the scalar span of
all the symbolic generator determinants. -/
theorem degreeOf_mem_span_det_column_family_le_one
    {K n J σ : Type*} [Field K] [Fintype n] [DecidableEq n] [DecidableEq J]
    (g : J → n → MvPolynomial σ K) (j₀ : J) (v : σ)
    (hdeg : ∀ j i, degreeOf v (g j i) ≤ if j = j₀ then 1 else 0)
    {P : MvPolynomial σ K}
    (hP : P ∈ Submodule.span K
      (Set.range (fun s : n → J => Matrix.det (Matrix.of (fun i k => g (s k) i))))) :
    degreeOf v P ≤ 1 := by
  classical
  induction hP using Submodule.span_induction with
  | mem p hp =>
      obtain ⟨s, rfl⟩ := hp
      exact degreeOf_det_column_family_le_one g j₀ v hdeg s
  | zero => simp
  | add p q hp hq ihp ihq =>
      exact (degreeOf_add_le v p q).trans (max_le ihp ihq)
  | smul a p hp ihp =>
      simpa only [Algebra.smul_def, algebraMap_eq] using
        (degreeOf_C_mul_le p v a).trans ihp

/-- Joint algebraic independence gives a unique polynomial representative
in any fixed scalar submodule of the polynomial algebra. -/
theorem existsUnique_polynomial_rep_of_mem_map
    {K L σ : Type*} [Field K] [CommRing L] [Algebra K L]
    (z : σ → L) (hz : AlgebraicIndependent K z)
    (S : Submodule K (MvPolynomial σ K)) {c : L}
    (hc : c ∈ S.map (MvPolynomial.aeval z).toLinearMap) :
    ∃! P : MvPolynomial σ K, P ∈ S ∧ MvPolynomial.aeval z P = c := by
  obtain ⟨P, hP, rfl⟩ := hc
  refine ⟨P, ⟨hP, rfl⟩, ?_⟩
  intro Q hQ
  exact hz hQ.2

/-- A scalar submodule of polynomials with individual variable degree at most
one has a square-scalar gap after an algebraically independent evaluation. -/
theorem aeval_square_scalar_gap
    {K L σ : Type*} [Field K] [CommRing L] [Algebra K L]
    (z : σ → L) (hz : AlgebraicIndependent K z)
    (S : Submodule K (MvPolynomial σ K)) (v : σ)
    (hdeg : ∀ P ∈ S, degreeOf v P ≤ 1)
    {c : L} (hc : c ∈ S.map (MvPolynomial.aeval z).toLinearMap)
    (hsc : z v ^ 2 * c ∈ S.map (MvPolynomial.aeval z).toLinearMap) : c = 0 := by
  classical
  obtain ⟨P, hP, hPc⟩ := hc
  obtain ⟨Q, hQ, hQc⟩ := hsc
  change MvPolynomial.aeval z P = c at hPc
  change MvPolynomial.aeval z Q = z v ^ 2 * c at hQc
  have heq : (X v : MvPolynomial σ K) ^ 2 * P = Q := by
    apply hz
    simpa only [map_mul, map_pow, aeval_X, hPc] using hQc.symm
  by_cases hzero : P = 0
  · simpa [hzero] using hPc.symm
  · have hbound := hdeg Q hQ
    rw [← heq, degreeOf_mul_eq (pow_ne_zero 2 (X_ne_zero v)) hzero,
      degreeOf_X_self_pow] at hbound
    omega

/-- The literal scalar-image intersection form of the auxiliary-scalar gap. -/
theorem aeval_square_scalar_image_intersection
    {K L σ : Type*} [Field K] [CommRing L] [Algebra K L]
    (z : σ → L) (hz : AlgebraicIndependent K z)
    (S : Submodule K (MvPolynomial σ K)) (v : σ)
    (hdeg : ∀ P ∈ S, degreeOf v P ≤ 1) :
    (fun c : L => z v ^ 2 * c) ''
        (S.map (MvPolynomial.aeval z).toLinearMap : Set L) ∩
        (S.map (MvPolynomial.aeval z).toLinearMap : Set L) = {0} := by
  ext c
  constructor
  · rintro ⟨⟨d, hd, rfl⟩, hsd⟩
    have hd0 := aeval_square_scalar_gap z hz S v hdeg hd hsd
    simp [hd0]
  · intro hc
    have hc0 : c = 0 := Set.mem_singleton_iff.mp hc
    subst c
    exact ⟨⟨0, Submodule.zero_mem _, by simp⟩, Submodule.zero_mem _⟩

end AlternatingAnalytic
