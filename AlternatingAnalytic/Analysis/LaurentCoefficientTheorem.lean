import AlternatingAnalytic.Analysis.LaurentCompletedCoefficient

/-! The complete bundled specification of the paper's completed Laurent coefficient map. -/

open scoped NNReal BoundedContinuousFunction

namespace AlternatingAnalytic

variable (κ : Type*) [Field κ] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)]
variable (S : Type*) [TopologicalSpace S] [DiscreteTopology S] (k : ℕ)

/-- The actual coefficient-field linear map on the completed projective exterior target
has the prescribed constant-coefficient array, the sharp support bound, pointwise
uniqueness, and recovery of every constant wedge. Linearity is part of the map's type. -/
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
