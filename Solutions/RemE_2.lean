import AlternatingAnalytic.Analysis.LaurentField
import AlternatingAnalytic.Analysis.ProjectiveExterior
import AlternatingAnalytic.Analysis.EquivalentUltrametric
import AlternatingAnalytic.Analysis.CompletedBaseChange
import Mathlib.Analysis.Analytic.Basic
import AlternatingAnalytic.Analysis.BaseChangeCompleteSelf
import AlternatingAnalytic.Analysis.LaurentResidueLift

/-!
# Remark E.2 (the case `K₁ = K̂`; direct `F_q((u))` route), p. 48

Solution: the statements of `Challenges/RemE_2.lean`, proved from the library:
* part 1: `AlternatingAnalytic.completedBaseChangeEmbedding_surjective_self`
  (`BaseChangeCompleteSelf.lean`): every tensor in `V ⊗_K K` is `rid u ⊗ 1`, so `ι_V` has dense
  range, and its range is closed since `V` is complete;
* part 2: `AlternatingAnalytic.isUltrametricDist_completedBaseChange_boundedSeq_self`
  (`BaseChangeCompleteSelf.lean`), transporting the sup ultrametric through `ι_V`;
* part 3: `AlternatingAnalytic.laurent_not_analyticAt` (`LaurentResidueLift.lean`) and
  `AlternatingAnalytic.laurentExterior_not_hasEquivalentUltrametricNorm`
  (`LaurentCompletedCoefficient.lean`).
-/

set_option backward.isDefEq.respectTransparency false

open scoped NNReal BoundedContinuousFunction

namespace AlternatingAnalyticChallenge.RemE_2

open AlternatingAnalytic

universe u

/-- Remark E.2, part 1: when `K₁ = K'`, the completed projective base change of a Banach space
`V` is identified isometrically with `V` by `ι_V`. -/
theorem completedBaseChangeEmbedding_surjective_self
    (K V : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    [SphericallyCompleteSpace K] [NormedAddCommGroup V] [NormedSpace K V] [CompleteSpace V] :
    Function.Surjective (completedBaseChangeEmbedding K V K) :=
  AlternatingAnalytic.completedBaseChangeEmbedding_surjective_self K V

/-- Remark E.2, part 2: when `K₁ = K'`, the source `E = ℓ^∞(ℕ, K₁) ⊗̂_π K₁` is nonarchimedean. -/
theorem isUltrametricDist_completedBaseChange_self
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    [SphericallyCompleteSpace K] :
    IsUltrametricDist (CompletedBaseChange K (ℕ →ᵇ K) K) :=
  AlternatingAnalytic.isUltrametricDist_completedBaseChange_boundedSeq_self K

/-- Remark E.2, part 3: over `K = F_q((u))` (here `LaurentField κ r`, `κ` finite of
characteristic `p`), Theorem 6.1(1) holds with `E = ℓ^∞(ℕ, K)` and `F = B` for every `k ≥ p`. -/
theorem laurent_direct_counterexample
    (κ : Type u) [Field κ] [Finite κ] (p : ℕ) (hp : p.Prime) [CharP κ p]
    (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] (k : ℕ) (hpk : p ≤ k) :
    (∀ f₀ : (ℕ →ᵇ LaurentField κ r) →L[LaurentField κ r] (ℕ →ᵇ LaurentField κ r),
      ¬ AnalyticAt (LaurentField κ r)
        (fun f : (ℕ →ᵇ LaurentField κ r) →L[LaurentField κ r] (ℕ →ᵇ LaurentField κ r) =>
          (ContinuousAlternatingMap.compContinuousLinearMapCLM f :
            ((ℕ →ᵇ LaurentField κ r) [⋀^Fin k]→L[LaurentField κ r]
                ProjectiveExteriorCompletion (LaurentField κ r) ℕ k) →L[LaurentField κ r]
              ((ℕ →ᵇ LaurentField κ r) [⋀^Fin k]→L[LaurentField κ r]
                ProjectiveExteriorCompletion (LaurentField κ r) ℕ k))) f₀) ∧
      ¬ HasEquivalentUltrametricNorm (LaurentField κ r)
        (ProjectiveExteriorCompletion (LaurentField κ r) ℕ k) := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact ⟨fun f₀ => AlternatingAnalytic.laurent_not_analyticAt κ r k p hpk f₀,
    AlternatingAnalytic.laurentExterior_not_hasEquivalentUltrametricNorm κ r k
      (hp.two_le.trans hpk)⟩

end AlternatingAnalyticChallenge.RemE_2
