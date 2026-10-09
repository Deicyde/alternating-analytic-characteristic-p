import AlternatingAnalytic.Analysis.LaurentBlockNorms
import AlternatingAnalytic.Analysis.UnitSumGrowth
import AlternatingAnalytic.Analysis.LaurentCoefficients
import AlternatingAnalytic.Analysis.ProjectiveExterior
import AlternatingAnalytic.Analysis.EquivalentUltrametric
import AlternatingAnalytic.Analysis.CompletedBaseChange

/-!
# Proof of Proposition E.1

Uses the block-norm estimates of `AlternatingAnalytic/Analysis/LaurentBlockNorms.lean`,
`laurentExterior_hasLinearUnitSumGrowth` and `laurentExterior_not_hasEquivalentUltrametricNorm`
from `LaurentCompletedCoefficient.lean`, and `HasLinearUnitSumGrowth` from `UnitSumGrowth.lean`.
-/

noncomputable section

open scoped NNReal BoundedContinuousFunction

namespace AlternatingAnalyticChallenge.PropE_1

open AlternatingAnalytic

universe u

variable (κ : Type u) [Field κ] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] (k : ℕ)

/-- The unit vector `e_n ∈ E₀ = κ^ℕ ⊆ E₁ = ℓ^∞(ℕ, K₁)`, with entries embedded as constant
Laurent series. -/
def unitVector (n : ℕ) : ℕ →ᵇ LaurentField κ r :=
  constantLaurentArray κ r (Pi.single n (1 : κ))

/-- The block wedge `ω_j = e_{kj+1} ∧ ⋯ ∧ e_{kj+k}` in `B`. -/
def blockWedge (j : ℕ) : ProjectiveExteriorCompletion (LaurentField κ r) ℕ k :=
  completedExteriorWedge (LaurentField κ r) ℕ k
    (fun i : Fin k => unitVector κ r (k * j + i.val + 1))

/-- The constant `M_r = max_{l ∈ ℕ} (l + 1) r^l`, written as a supremum. -/
def weightMax : ℝ := ⨆ l : ℕ, ((l : ℝ) + 1) * (r : ℝ) ^ l

/-- Proposition E.1: every block wedge has norm one. -/
theorem norm_blockWedge (hk : 2 ≤ k) (j : ℕ) : ‖blockWedge κ r k j‖ = 1 :=
  norm_laurentBlockWedge κ r k j

/-- Proposition E.1: `N / M_r ≤ ‖∑_{j<N} ω_j‖_B ≤ N` for `N ≥ 1`. -/
theorem blockWedge_sum_bounds (hk : 2 ≤ k) (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) / weightMax r ≤ ‖∑ j ∈ Finset.range N, blockWedge κ r k j‖ ∧
      ‖∑ j ∈ Finset.range N, blockWedge κ r k j‖ ≤ (N : ℝ) := by
  have hM : weightMax r = geometricWeightMaximum r := by
    have hbdd : BddAbove (Set.range fun l : ℕ => ((l : ℝ) + 1) * (r : ℝ) ^ l) := by
      refine ⟨geometricWeightMaximum r, ?_⟩
      rintro _ ⟨l, rfl⟩
      exact geometricWeight_le_maximum r l
    apply le_antisymm
    · exact ciSup_le (geometricWeight_le_maximum r)
    · unfold geometricWeightMaximum
      exact le_ciSup hbdd _
  rw [hM]
  exact ⟨le_norm_sum_laurentBlockWedge κ r k hk N, norm_sum_laurentBlockWedge_le κ r k N⟩

/-- Proposition E.1: the norm of `B` is not nonarchimedean. -/
theorem not_isUltrametricDist_B (hk : 2 ≤ k) :
    ¬ IsUltrametricDist (ProjectiveExteriorCompletion (LaurentField κ r) ℕ k) := by
  intro hU
  exact laurentExterior_not_hasEquivalentUltrametricNorm κ r k hk
    ⟨normSeminorm _ _, fun x y => IsUltrametricDist.norm_add_le_max x y,
      ⟨1, one_pos, fun x => by simp⟩, ⟨1, one_pos, fun x => by simp⟩⟩

/-- Proposition E.1: `B` admits no equivalent nonarchimedean norm (over `K₁`). -/
theorem not_hasEquivalentUltrametricNorm_B (hk : 2 ≤ k) :
    ¬ HasEquivalentUltrametricNorm (LaurentField κ r)
      (ProjectiveExteriorCompletion (LaurentField κ r) ℕ k) :=
  laurentExterior_not_hasEquivalentUltrametricNorm κ r k hk

/-- Proposition E.1: for `K' ⊇ K₁` satisfying (H1) and (H2), the norm of
`F = B ⊗̂_π K'` is not nonarchimedean. -/
theorem not_isUltrametricDist_F (hk : 2 ≤ k)
    (K' : Type u) [NontriviallyNormedField K'] [NormedAlgebra (LaurentField κ r) K']
    [IsUltrametricDist K'] :
    ¬ IsUltrametricDist (CompletedBaseChange (LaurentField κ r)
      (ProjectiveExteriorCompletion (LaurentField κ r) ℕ k) K') := by
  intro hU
  exact ((laurentExterior_hasLinearUnitSumGrowth κ r k hk).map
    (completedBaseChangeEmbedding (LaurentField κ r)
      (ProjectiveExteriorCompletion (LaurentField κ r) ℕ k) K').toLinearMap.toAddMonoidHom
    (completedBaseChangeEmbedding (LaurentField κ r)
      (ProjectiveExteriorCompletion (LaurentField κ r) ℕ k) K').isometry).not_hasEquivalentUltrametricNorm K'
    ⟨normSeminorm _ _, fun x y => IsUltrametricDist.norm_add_le_max x y,
      ⟨1, one_pos, fun x => by simp⟩, ⟨1, one_pos, fun x => by simp⟩⟩

/-- Proposition E.1: for `K' ⊇ K₁` satisfying (H1) and (H2), `F = B ⊗̂_π K'` admits no
equivalent nonarchimedean norm over `K'` or over any subfield `K₀` of `K'`. -/
theorem not_hasEquivalentUltrametricNorm_F (hk : 2 ≤ k)
    (K' : Type u) [NontriviallyNormedField K'] [NormedAlgebra (LaurentField κ r) K']
    [IsUltrametricDist K']
    (K₀ : Type*) [NormedField K₀] [NormedAlgebra K₀ K']
    [NormedSpace K₀ (CompletedBaseChange (LaurentField κ r)
      (ProjectiveExteriorCompletion (LaurentField κ r) ℕ k) K')]
    [IsScalarTower K₀ K' (CompletedBaseChange (LaurentField κ r)
      (ProjectiveExteriorCompletion (LaurentField κ r) ℕ k) K')] :
    ¬ HasEquivalentUltrametricNorm K₀ (CompletedBaseChange (LaurentField κ r)
      (ProjectiveExteriorCompletion (LaurentField κ r) ℕ k) K') :=
  ((laurentExterior_hasLinearUnitSumGrowth κ r k hk).map
    (completedBaseChangeEmbedding (LaurentField κ r)
      (ProjectiveExteriorCompletion (LaurentField κ r) ℕ k) K').toLinearMap.toAddMonoidHom
    (completedBaseChangeEmbedding (LaurentField κ r)
      (ProjectiveExteriorCompletion (LaurentField κ r) ℕ k) K').isometry).not_hasEquivalentUltrametricNorm K₀

end AlternatingAnalyticChallenge.PropE_1
