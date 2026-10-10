import AlternatingAnalytic.Analysis.FiniteCoordinateDomain
import AlternatingAnalytic.Analysis.FiniteCoordinateCodomain
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Finite-dimensional spaces over a complete field

Over a complete field, linear functionals on a finite-dimensional space are bounded and
the space is complete (Lemma A.3). So the coordinates of `Module.finBasis` are
continuous, and Proposition 4.1(2) makes `A^k` continuously polynomial whenever `E` or
`E'` is finite-dimensional, as remarked after Proposition 4.1. Here `A^k` is
`LiftCriterion.Q`.
-/

namespace AlternatingAnalytic

variable {K E E' F : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup E'] [NormedSpace K E']
  [NormedAddCommGroup F] [NormedSpace K F]

section CompleteField

variable [CompleteSpace K]

/-- Every linear functional on a finite-dimensional space is bounded. -/
theorem bounded_linearFunctional_of_finiteDimensional [FiniteDimensional K E]
    (ℓ : E →ₗ[K] K) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, ‖ℓ x‖ ≤ C * ‖x‖ := by
  let ℓc : E →L[K] K := ⟨ℓ, ℓ.continuous_of_finiteDimensional⟩
  exact ⟨‖ℓc‖, norm_nonneg _, ℓc.le_opNorm⟩

/-- Lemma A.3: linear functionals are bounded and the space is complete. -/
theorem finiteDimensional_bounded_and_complete [FiniteDimensional K E] :
    (∀ ℓ : E →ₗ[K] K, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, ‖ℓ x‖ ≤ C * ‖x‖) ∧
      CompleteSpace E :=
  ⟨bounded_linearFunctional_of_finiteDimensional, FiniteDimensional.complete K E⟩

/-- The canonical finite basis has continuous coordinate functionals. -/
theorem continuous_finBasis_coord [FiniteDimensional K E]
    (i : Fin (Module.finrank K E)) : Continuous ((Module.finBasis K E).coord i) :=
  ((Module.finBasis K E).coord i).continuous_of_finiteDimensional

/-- If `E` is finite-dimensional, `A^k` is continuously polynomial. -/
theorem cpolynomialAt_Q_of_finiteDimensionalDomain [FiniteDimensional K E]
    (k : ℕ) (f₀ : E →L[K] E') :
    CPolynomialAt K (LiftCriterion.Q K (Fin k) E E' F) f₀ :=
  cpolynomialAt_Q_of_finiteCoordinateDomain (Module.finBasis K E)
    continuous_finBasis_coord k f₀

/-- If `E` is finite-dimensional, `A^k` is analytic. -/
theorem analyticAt_Q_of_finiteDimensionalDomain [FiniteDimensional K E]
    (k : ℕ) (f₀ : E →L[K] E') :
    AnalyticAt K (LiftCriterion.Q K (Fin k) E E' F) f₀ :=
  (cpolynomialAt_Q_of_finiteDimensionalDomain k f₀).analyticAt

/-- If `E'` is finite-dimensional, `A^k` is continuously polynomial. -/
theorem cpolynomialAt_Q_of_finiteDimensionalCodomain [FiniteDimensional K E']
    (k : ℕ) (f₀ : E →L[K] E') :
    CPolynomialAt K (LiftCriterion.Q K (Fin k) E E' F) f₀ :=
  cpolynomialAt_Q_of_finiteCoordinateCodomain (Module.finBasis K E')
    continuous_finBasis_coord k f₀

/-- If `E'` is finite-dimensional, `A^k` is analytic. -/
theorem analyticAt_Q_of_finiteDimensionalCodomain [FiniteDimensional K E']
    (k : ℕ) (f₀ : E →L[K] E') :
    AnalyticAt K (LiftCriterion.Q K (Fin k) E E' F) f₀ :=
  (cpolynomialAt_Q_of_finiteDimensionalCodomain k f₀).analyticAt

/-- If `E` or `E'` is finite-dimensional, `A^k` is continuously polynomial and
analytic at every point, in every degree. -/
theorem finiteDimensional_positive
    (h : FiniteDimensional K E ∨ FiniteDimensional K E') :
    ∀ (k : ℕ) (f₀ : E →L[K] E'),
      CPolynomialAt K (LiftCriterion.Q K (Fin k) E E' F) f₀ ∧
        AnalyticAt K (LiftCriterion.Q K (Fin k) E E' F) f₀ := by
  intro k f₀
  rcases h with h | h
  · let := h
    exact ⟨cpolynomialAt_Q_of_finiteDimensionalDomain k f₀,
      analyticAt_Q_of_finiteDimensionalDomain k f₀⟩
  · let := h
    exact ⟨cpolynomialAt_Q_of_finiteDimensionalCodomain k f₀,
      analyticAt_Q_of_finiteDimensionalCodomain k f₀⟩

end CompleteField

end AlternatingAnalytic
