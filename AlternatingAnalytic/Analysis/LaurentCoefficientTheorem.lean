import AlternatingAnalytic.Analysis.LaurentCompletedCoefficient

/-!
# Proposition C.3

All properties of the coefficient map `η` on the completed projective exterior power `B`,
in one statement.
-/

open scoped NNReal BoundedContinuousFunction

namespace AlternatingAnalytic

variable (κ : Type*) [Field κ] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)]
variable (S : Type*) [TopologicalSpace S] [DiscreteTopology S] (k : ℕ)

/-- Proposition C.3: the `κ`-linear map `η` on `B` satisfies `Ω^κ(η b) = coeff₀(J b)`, is
unique with this property, satisfies `sdim (η b) ≤ k M_r ‖b‖`, and sends a wedge of
constant arrays to the same wedge over `κ`. -/
theorem completedLaurentCoefficient_full_properties (α : Fin k) :
    (∀ b : ProjectiveExteriorCompletion (LaurentField κ r) S k,
      determinantArray (completedLaurentCoefficient κ r S k α b) =
        boundedLaurentCoeff κ r 0 (completedExteriorArray (LaurentField κ r) S k b)) ∧
    (∀ b : ProjectiveExteriorCompletion (LaurentField κ r) S k,
      (exteriorSupportDim (completedLaurentCoefficient κ r S k α b) : ℝ) ≤
        (k : ℝ) * geometricWeightMaximum r * ‖b‖) ∧
    (∀ (b : ProjectiveExteriorCompletion (LaurentField κ r) S k)
      (β : ⋀[κ]^k (S → κ)),
      determinantArray β =
        boundedLaurentCoeff κ r 0 (completedExteriorArray (LaurentField κ r) S k b) →
      β = completedLaurentCoefficient κ r S k α b) ∧
    (∀ x : Fin k → (S → κ),
      completedLaurentCoefficient κ r S k α
        (completedExteriorWedge (LaurentField κ r) S k
          (fun i => constantLaurentArray κ r (x i))) =
        exteriorPower.ιMulti κ k x) :=
  ⟨completedLaurentCoefficient_array κ r S k α,
    completedLaurentCoefficient_support_le κ r S k α,
    completedLaurentCoefficient_unique κ r S k α,
    completedLaurentCoefficient_constant_wedge κ r S k α⟩

end AlternatingAnalytic
