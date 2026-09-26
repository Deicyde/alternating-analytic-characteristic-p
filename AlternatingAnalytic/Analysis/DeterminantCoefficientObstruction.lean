import AlternatingAnalytic.Algebra.DeterminantQuadraticGap

/-!
# Algebraic obstruction in the actual determinant coefficient space

The unique polynomial representatives and auxiliary specialization are used only
algebraically. No continuity of either map is asserted or needed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators NNReal

namespace AlternatingAnalytic.DeterminantPair

variable (p : ℕ) [Fact p.Prime] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)]
attribute [local instance] preferredNormedFieldK preferredFieldK preferredFieldL

/-- Specialization carries an original scalar relation into the polynomial
coefficient space, by injectivity of evaluation on polynomial representatives. -/
theorem specializeCoefficient_relation
    (b : Fin p → C p r)
    (hsum : (∑ i : Fin p, z p r (Sum.inl i) * (b i : L p r)) ∈ C p r) :
    (∑ i : Fin p, MvPolynomial.X i *
      (specializeCoefficient p r (b i) : Poly0 p r)) ∈ C0poly p r := by
  let P : Fin p → Poly p r := fun i => (polynomialEquivC p r).symm (b i)
  have hP : (∑ i : Fin p, MvPolynomial.X (Sum.inl i) * P i) ∈ Cpoly p r := by
    apply (evaluation_mem_C_iff p r _).mp
    simpa only [map_sum, map_mul, evaluation_X, P,
      evaluation_polynomialEquivC_symm] using hsum
  have h := specialization_mem_Cpoly p r hP
  simpa only [map_sum, map_mul, specialization_X, P,
    ← specializeCoefficient_apply] using h

/-- There are no original small-target coefficients with constant term one
whose primary-coordinate combination still belongs to the small target. -/
theorem no_scalar_coefficient_family :
    ¬ ∃ b : Fin p → C p r, (b 0 : L p r) = 1 ∧
      (∑ i : Fin p, z p r (Sum.inl i) * (b i : L p r)) ∈ C p r := by
  rintro ⟨b, hb0, hsum⟩
  apply no_coefficient_family p r
  refine ⟨fun i => specializeCoefficient p r (b i), ?_,
    specializeCoefficient_relation p r b hsum⟩
  have hb : b 0 = ⟨1, one_mem_C p r⟩ := Subtype.ext hb0
  change (specializeCoefficient p r (b 0) : Poly0 p r) = 1
  rw [hb, specializeCoefficient_one]

end AlternatingAnalytic.DeterminantPair
