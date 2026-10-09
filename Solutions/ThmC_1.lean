import AlternatingAnalytic.Analysis.LaurentField
import AlternatingAnalytic.Analysis.ProjectiveExterior
import AlternatingAnalytic.Analysis.LaurentResidueLift

/-!
# Theorem C.1 (no bounded lift over a Laurent series field), p. 36

Solution: both parts are `AlternatingAnalytic.laurent_not_hasBoundedLift` and
`AlternatingAnalytic.laurent_not_analyticAt` (`Analysis/LaurentResidueLift.lean`), with the lift
re-indexed by `Round24Transfer.hasBoundedLift_iff_exists_ι`.
-/

set_option backward.isDefEq.respectTransparency false

open scoped NNReal BoundedContinuousFunction

namespace AlternatingAnalyticChallenge.ThmC_1

open AlternatingAnalytic

universe u

/-- Precomposition `A^k_{E,E;F} : f ↦ (m ↦ m ∘ (f, …, f))` admits a bounded `k`-linear lift:
a continuous `k`-linear map on `L(E,E)` whose diagonal is `A`. -/
def HasBoundedKLinearLift (K : Type*) [NontriviallyNormedField K]
    (E F : Type*) [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup F] [NormedSpace K F] (k : ℕ) : Prop :=
  ∃ P : ContinuousMultilinearMap K (fun _ : Fin k => E →L[K] E)
      ((E [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F)),
    ∀ f : E →L[K] E, P (fun _ => f) = ContinuousAlternatingMap.compContinuousLinearMapCLM f

/-- **Theorem C.1, main part.** Over `K₁ = κ((X))` with `κ` finite of characteristic `p ≤ k`,
precomposition on `Alt^k(ℓ^∞(ℕ,K₁); B)` has no bounded `k`-linear lift. -/
theorem part1_not_hasBoundedKLinearLift
    (κ : Type u) [Field κ] [Finite κ] (p : ℕ) (hp : p.Prime) [CharP κ p]
    (k : ℕ) (hpk : p ≤ k) (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] :
    ¬ HasBoundedKLinearLift (LaurentField κ r) (ℕ →ᵇ LaurentField κ r)
      (ProjectiveExteriorCompletion (LaurentField κ r) ℕ k) k := by
  have : Fact p.Prime := ⟨hp⟩
  rintro ⟨P, hP⟩
  exact laurent_not_hasBoundedLift κ r k p hpk
    (Round24Transfer.hasBoundedLift_iff_exists_ι.2 ⟨P, hP⟩)

/-- **Theorem C.1, consequence.** The same precomposition map is analytic at no point of
`L(E₁, E₁)`. -/
theorem part2_not_analyticAt
    (κ : Type u) [Field κ] [Finite κ] (p : ℕ) (hp : p.Prime) [CharP κ p]
    (k : ℕ) (hpk : p ≤ k) (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)]
    (f₀ : (ℕ →ᵇ LaurentField κ r) →L[LaurentField κ r] (ℕ →ᵇ LaurentField κ r)) :
    ¬ AnalyticAt (LaurentField κ r)
      (fun f : (ℕ →ᵇ LaurentField κ r) →L[LaurentField κ r] (ℕ →ᵇ LaurentField κ r) =>
        (ContinuousAlternatingMap.compContinuousLinearMapCLM f :
          ((ℕ →ᵇ LaurentField κ r) [⋀^Fin k]→L[LaurentField κ r]
              ProjectiveExteriorCompletion (LaurentField κ r) ℕ k) →L[LaurentField κ r]
            ((ℕ →ᵇ LaurentField κ r) [⋀^Fin k]→L[LaurentField κ r]
              ProjectiveExteriorCompletion (LaurentField κ r) ℕ k))) f₀ := by
  have : Fact p.Prime := ⟨hp⟩
  exact laurent_not_analyticAt κ r k p hpk f₀

end AlternatingAnalyticChallenge.ThmC_1
