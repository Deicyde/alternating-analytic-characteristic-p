import AlternatingAnalytic.Algebra.DeterminantQuadraticBasic

/-! # Homogeneous components of the determinant coefficient spaces -/

noncomputable section
open scoped BigOperators

namespace AlternatingAnalytic.DeterminantQuadratic

variable (K : Type*) [Field K] (p : ℕ)

theorem genPoly_isHomogeneous (g : GeneratorIndex p) (r : Fin p) :
    (genPoly K p g r).IsHomogeneous (generatorDegree p g) := by
  classical
  rcases g with i | (i | u)
  · simp only [genPoly, generatorDegree]
    split_ifs
    · exact MvPolynomial.isHomogeneous_one _ _
    · exact MvPolynomial.isHomogeneous_zero _ _ _
  · simp only [genPoly, generatorDegree]
    apply MvPolynomial.IsHomogeneous.sum
    intro j hj
    split_ifs
    · exact MvPolynomial.isHomogeneous_X _ _
    · exact MvPolynomial.isHomogeneous_zero _ _ _
  · simp only [genPoly, generatorDegree]
    apply MvPolynomial.IsHomogeneous.sum
    intro i hi
    apply MvPolynomial.IsHomogeneous.sum
    intro j hj
    split_ifs
    · exact (MvPolynomial.isHomogeneous_X K i).mul (MvPolynomial.isHomogeneous_X K j)
    · exact MvPolynomial.isHomogeneous_zero _ _ _

theorem detPoly_isHomogeneous (s : Fin p → GeneratorIndex p) :
    (detPoly K p s).IsHomogeneous (∑ j, generatorDegree p (s j)) := by
  classical
  rw [detPoly, Matrix.det_apply']
  apply MvPolynomial.IsHomogeneous.sum
  intro σ hσ
  have hp : (∏ j : Fin p, genPoly K p (s j) (σ j)).IsHomogeneous
      (∑ j, generatorDegree p (s j)) :=
    MvPolynomial.IsHomogeneous.prod _ _ _ (fun j _ => genPoly_isHomogeneous K p (s j) (σ j))
  simpa only [map_intCast, Matrix.of_apply] using hp.C_mul (↑(Equiv.Perm.sign σ) : K)

theorem homogeneousComponent_mem_G0poly (n : ℕ) {P : Poly K p}
    (hP : P ∈ G0poly K p) : MvPolynomial.homogeneousComponent n P ∈ G0poly K p := by
  classical
  induction hP using Submodule.span_induction with
  | mem Q hQ =>
    obtain ⟨s, rfl⟩ := hQ
    rw [MvPolynomial.homogeneousComponent_of_mem (detPoly_isHomogeneous K p s)]
    split_ifs
    · exact Submodule.subset_span ⟨s, rfl⟩
    · exact Submodule.zero_mem _
  | zero => simp
  | add Q R hQ hR ihQ ihR => simpa using (G0poly K p).add_mem ihQ ihR
  | smul c Q hQ ihQ => simpa using (G0poly K p).smul_mem c ihQ

/-- Multiplication by one variable shifts the total homogeneous component by one. -/
theorem homogeneousComponent_X_mul (n : ℕ) (i : Fin p) (P : Poly K p) :
    MvPolynomial.homogeneousComponent (n + 1) (MvPolynomial.X i * P) =
      MvPolynomial.X i * MvPolynomial.homogeneousComponent n P := by
  classical
  ext m
  by_cases hi : i ∈ m.support
  · have hle : Finsupp.single i 1 ≤ m := by
      rw [Finsupp.single_le_iff]
      exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
    have hm : Finsupp.single i 1 + (m - Finsupp.single i 1) = m :=
      add_tsub_cancel_of_le hle
    have hd : m.degree = 1 + (m - Finsupp.single i 1).degree := by
      calc
        m.degree = (Finsupp.single i 1 + (m - Finsupp.single i 1)).degree :=
          congrArg Finsupp.degree hm.symm
        _ = 1 + (m - Finsupp.single i 1).degree := by rw [map_add, Finsupp.degree_single]
      rfl
    have heq : m.degree = n + 1 ↔ (m - Finsupp.single i 1).degree = n := by omega
    simp only [MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_X_mul', hi,
      ite_true, heq]
  · simp [MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_X_mul', hi]

theorem homogeneousComponent_mem_C0poly (n : ℕ) {P : Poly K p}
    (hP : P ∈ C0poly K p) : MvPolynomial.homogeneousComponent n P ∈ C0poly K p := by
  rw [mem_C0poly] at hP ⊢
  refine ⟨homogeneousComponent_mem_G0poly K p n hP.1, fun i => ?_⟩
  rw [← homogeneousComponent_X_mul]
  exact homogeneousComponent_mem_G0poly K p (n + 1) (hP.2 i)

end AlternatingAnalytic.DeterminantQuadratic
