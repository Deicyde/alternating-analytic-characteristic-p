import AlternatingAnalytic.Analysis.FiniteCoordinateDomain
import AlternatingAnalytic.Analysis.FiniteCoordinateCodomain
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Finite-dimensional operator positivity over complete fields

The finite-dimensional lemma and positivity corollary of `charp.tex`,
`lem:findim` and `cor:finite-dimensional-positive`. Completeness of the scalar
field makes the coordinates of `Module.finBasis` continuous, so either finite
coordinate construction applies. All degrees, including zero, are covered.
No completeness assumption on the three normed spaces is needed.
-/

namespace AlternatingAnalytic

variable {K E E' F : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup E'] [NormedSpace K E']
  [NormedAddCommGroup F] [NormedSpace K F]

section CompleteField

variable [CompleteSpace K]

/-- Every linear functional on a finite-dimensional space has a nonnegative norm bound. -/
theorem bounded_linearFunctional_of_finiteDimensional [FiniteDimensional K E]
    (ℓ : E →ₗ[K] K) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, ‖ℓ x‖ ≤ C * ‖x‖ := by
  let ℓc : E →L[K] K := ⟨ℓ, ℓ.continuous_of_finiteDimensional⟩
  exact ⟨‖ℓc‖, norm_nonneg _, ℓc.le_opNorm⟩

/-- Both conclusions of `lem:findim`: bounded linear functionals and completeness. -/
theorem finiteDimensional_bounded_and_complete [FiniteDimensional K E] :
    (∀ ℓ : E →ₗ[K] K, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, ‖ℓ x‖ ≤ C * ‖x‖) ∧
      CompleteSpace E :=
  ⟨bounded_linearFunctional_of_finiteDimensional, FiniteDimensional.complete K E⟩

/-- The canonical finite basis has continuous coordinate functionals. -/
theorem continuous_finBasis_coord [FiniteDimensional K E]
    (i : Fin (Module.finrank K E)) : Continuous ((Module.finBasis K E).coord i) :=
  ((Module.finBasis K E).coord i).continuous_of_finiteDimensional

/-- Finite-dimensional source spaces give continuous polynomiality in every degree. -/
theorem cpolynomialAt_Q_of_finiteDimensionalDomain [FiniteDimensional K E]
    (k : ℕ) (f₀ : E →L[K] E') :
    CPolynomialAt K (Round24Transfer.Q K (Fin k) E E' F) f₀ :=
  cpolynomialAt_Q_of_finiteCoordinateDomain (Module.finBasis K E)
    continuous_finBasis_coord k f₀

/-- Finite-dimensional source spaces give analyticity in every degree. -/
theorem analyticAt_Q_of_finiteDimensionalDomain [FiniteDimensional K E]
    (k : ℕ) (f₀ : E →L[K] E') :
    AnalyticAt K (Round24Transfer.Q K (Fin k) E E' F) f₀ :=
  (cpolynomialAt_Q_of_finiteDimensionalDomain k f₀).analyticAt

/-- Finite-dimensional operator codomains give continuous polynomiality in every degree. -/
theorem cpolynomialAt_Q_of_finiteDimensionalCodomain [FiniteDimensional K E']
    (k : ℕ) (f₀ : E →L[K] E') :
    CPolynomialAt K (Round24Transfer.Q K (Fin k) E E' F) f₀ :=
  cpolynomialAt_Q_of_finiteCoordinateCodomain (Module.finBasis K E')
    continuous_finBasis_coord k f₀

/-- Finite-dimensional operator codomains give analyticity in every degree. -/
theorem analyticAt_Q_of_finiteDimensionalCodomain [FiniteDimensional K E']
    (k : ℕ) (f₀ : E →L[K] E') :
    AnalyticAt K (Round24Transfer.Q K (Fin k) E E' F) f₀ :=
  (cpolynomialAt_Q_of_finiteDimensionalCodomain k f₀).analyticAt

/-- The complete positivity corollary: either finite-dimensional space suffices
for continuous polynomiality and analyticity at every point, in every degree. -/
theorem finiteDimensional_positive
    (h : FiniteDimensional K E ∨ FiniteDimensional K E') :
    ∀ (k : ℕ) (f₀ : E →L[K] E'),
      CPolynomialAt K (Round24Transfer.Q K (Fin k) E E' F) f₀ ∧
        AnalyticAt K (Round24Transfer.Q K (Fin k) E E' F) f₀ := by
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
