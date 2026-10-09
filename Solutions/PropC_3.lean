import AlternatingAnalytic.Analysis.LaurentField
import AlternatingAnalytic.Analysis.ProjectiveExterior
import AlternatingAnalytic.Algebra.ExteriorSupportDimension
import AlternatingAnalytic.Analysis.LaurentCoefficientTheorem

/-!
# Proof of Proposition C.3

`η` is `completedLaurentCoefficient κ r ℕ k 0`, with its properties
`completedLaurentCoefficient_array`, `_unique` and `_support_le`
(`Analysis/LaurentCompletedCoefficient.lean`).
-/

set_option backward.isDefEq.respectTransparency false

open scoped NNReal BoundedContinuousFunction

namespace AlternatingAnalyticChallenge.PropC_3

open AlternatingAnalytic

universe u

/-- The constant-coefficient map `coeff₀ : ℓ^∞(S, κ((X))) → κ^S`, taken coordinatewise. -/
noncomputable def coeff0 (κ : Type u) [Field κ] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] {S : Type*}
    [TopologicalSpace S] (y : S →ᵇ LaurentField κ r) : S → κ :=
  fun s => LaurentField.coeff κ r 0 (y s)

/-- `M_r := max_{l ∈ ℕ} (l + 1) r^l`. -/
noncomputable def Mr (r : ℝ≥0) : ℝ := ⨆ l : ℕ, ((l : ℝ) + 1) * (r : ℝ) ^ l

/-- Each `b ∈ B` has a unique `η(b) ∈ Λ^k_κ E₀` with `Ω^κ(η(b)) = coeff₀(J b)`; `η` is
`κ`-linear and `sdim(η(b)) ≤ k M_r ‖b‖`. -/
theorem support_estimate
    (κ : Type u) [Field κ] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] (k : ℕ) (hk : 1 ≤ k)
    (Ωκ : (⋀[κ]^k (ℕ → κ)) →ₗ[κ] ((Fin k → ℕ) → κ))
    (hΩκ : ∀ (y : Fin k → ℕ → κ) (c : Fin k → ℕ),
      Ωκ (exteriorPower.ιMulti κ k y) c = Matrix.det (fun a b => y b (c a))) :
    ∃ η : ProjectiveExteriorCompletion (LaurentField κ r) ℕ k → ⋀[κ]^k (ℕ → κ),
      (∀ b : ProjectiveExteriorCompletion (LaurentField κ r) ℕ k,
        Ωκ (η b) = coeff0 κ r (completedExteriorArray (LaurentField κ r) ℕ k b)) ∧
      (∀ (b : ProjectiveExteriorCompletion (LaurentField κ r) ℕ k) (β : ⋀[κ]^k (ℕ → κ)),
        Ωκ β = coeff0 κ r (completedExteriorArray (LaurentField κ r) ℕ k b) → β = η b) ∧
      (∀ b b' : ProjectiveExteriorCompletion (LaurentField κ r) ℕ k,
        η (b + b') = η b + η b') ∧
      (∀ (c : κ) (b : ProjectiveExteriorCompletion (LaurentField κ r) ℕ k),
        η (algebraMap κ (LaurentField κ r) c • b) = c • η b) ∧
      (∀ b : ProjectiveExteriorCompletion (LaurentField κ r) ℕ k,
        (exteriorSupportDim (η b) : ℝ) ≤ (k : ℝ) * Mr r * ‖b‖) := by
  have hΩ : Ωκ = determinantArray := by
    apply exteriorPower.linearMap_ext
    ext y c
    simp [hΩκ, determinantArray_ιMulti]
  subst hΩ
  have hb : BddAbove (Set.range fun l : ℕ => ((l : ℝ) + 1) * (r : ℝ) ^ l) :=
    ⟨geometricWeightMaximum r, Set.forall_mem_range.2 (geometricWeight_le_maximum r)⟩
  have hMr : Mr r = geometricWeightMaximum r := by
    apply le_antisymm (ciSup_le (geometricWeight_le_maximum r))
    unfold geometricWeightMaximum
    exact le_ciSup hb _
  let α : Fin k := ⟨0, by omega⟩
  refine ⟨completedLaurentCoefficient κ r ℕ k α, completedLaurentCoefficient_array κ r ℕ k α,
    completedLaurentCoefficient_unique κ r ℕ k α, fun b b' => map_add _ b b',
    fun c b => map_smul (completedLaurentCoefficient κ r ℕ k α) c b, fun b => ?_⟩
  rw [hMr]
  exact completedLaurentCoefficient_support_le κ r ℕ k α b

end AlternatingAnalyticChallenge.PropC_3
