import AlternatingAnalytic.Analysis.LaurentCoefficients
import AlternatingAnalytic.Analysis.ProjectiveExterior
import AlternatingAnalytic.Analysis.EquivalentUltrametric
import AlternatingAnalytic.Analysis.CompletedBaseChange

/-!
# Proposition E.1 (the target has no equivalent nonarchimedean norm), pp. 47-48

Paper statement (Appendix E). "Let `κ` be any field, `k ≥ 2`, `r ∈ (0,1)`, and let
`K₁ = κ((X))`, `E₁`, `E₀` and `B` be as in Appendix C. Let `e_i ∈ E₀` be the unit vectors and
`ω_j := e_{kj+1} ∧ ⋯ ∧ e_{kj+k} ∈ B` (`j ≥ 0`), wedges on pairwise disjoint blocks of indices.
Then `‖ω_j‖_B = 1` and `N / M_r ≤ ‖∑_{j<N} ω_j‖_B ≤ N` (`N ≥ 1`). Hence the norm of `B` is not
nonarchimedean, and `B` admits no equivalent nonarchimedean norm. The same holds for
`F = B ⊗̂_π K'` as in Appendix D, for any `K' ⊇ K₁` satisfying (H1) and (H2), regarded as a
normed space over `K'` or over any subfield of `K'`."

Here (Appendix C) `K₁ = κ((X))` has `|a| = r^{ord a}`, `E₁ = ℓ^∞(ℕ, K₁)` with the sup norm,
`E₀ = κ^ℕ ⊆ E₁`, `B` is the completion of `Λ^k_{K₁} E₁` under the projective exterior norm
`‖ω‖_π = inf ∑_j ∏_i ‖x_{j,i}‖_∞`, and `M_r = max_{l ∈ ℕ} (l + 1) r^l`.

## Formalization notes

* `K₁` is the library's `LaurentField κ r` (Laurent series `LaurentSeries κ` with
  `‖a‖ = r^{ord a}`; complete, nonarchimedean, spherically complete instances), with
  `r : ℝ≥0` and `Fact (0 < r)`, `Fact (r < 1)`. `E₁ = ℕ →ᵇ K₁`. `B` is the library's
  `ProjectiveExteriorCompletion K₁ ℕ k` (completion of `⋀[K₁]^k (ℕ →ᵇ K₁)` under the ordinary-sum
  projective exterior norm) and the wedge is `completedExteriorWedge`. These, and
  `constantLaurentArray` (the inclusion `κ^ℕ → E₁` by constant series), `CompletedBaseChange`
  (`F = B ⊗̂_π K'`) and `HasEquivalentUltrametricNorm`, are imported as definitions. The proving
  modules (`LaurentBlockNorms.lean`, `LaurentCompletedCoefficient.lean`, `UnitSumGrowth.lean`,
  `ExteriorBlocks.lean`) are not imported.
* Defined here: `unitVector n = e_n`, `blockWedge j = ω_j`, `weightMax r = M_r` (as the
  supremum `⨆ l, (l + 1) r^l`, which is the paper's maximum). Indices are in `ℕ = {0, 1, …}`;
  the blocks use indices `kj + 1, …, kj + k` exactly as in the paper (index `0` is unused).
* "Equivalent nonarchimedean norm" is `HasEquivalentUltrametricNorm K F`: a `K`-seminorm
  satisfying the ultrametric inequality with two-sided positive bounds against `‖·‖`.
  "The norm is not nonarchimedean" is `¬ IsUltrametricDist`.
* (H1) holds automatically for `K₁ = LaurentField κ r`; (H2) is `[IsUltrametricDist K']`, and
  `K₁ ⊆ K'` isometrically is `[NormedAlgebra K₁ K']`. `K'` lives in the universe of `κ`
  (library construction). "Regarded over any subfield `K₀` of `K'`" is a normed field `K₀` with
  `[NormedAlgebra K₀ K']` acting on `F` compatibly (`IsScalarTower K₀ K' F`); `K₀ = K'` is
  included.
* The hypothesis `k ≥ 2` is carried by every part, as in the paper.
-/

noncomputable section

open scoped NNReal BoundedContinuousFunction

namespace AlternatingAnalyticChallenge.PropE_1

open AlternatingAnalytic

universe u

variable (κ : Type u) [Field κ] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] (k : ℕ)

/-- The unit vector `e_n ∈ E₀ = κ^ℕ ⊆ E₁ = ℓ^∞(ℕ, K₁)` (entries in `κ`, embedded as constant
Laurent series). -/
def unitVector (n : ℕ) : ℕ →ᵇ LaurentField κ r :=
  constantLaurentArray κ r (Pi.single n (1 : κ))

/-- The block wedge `ω_j = e_{kj+1} ∧ ⋯ ∧ e_{kj+k}` in the Banach exterior target
`B = ProjectiveExteriorCompletion K₁ ℕ k`. -/
def blockWedge (j : ℕ) : ProjectiveExteriorCompletion (LaurentField κ r) ℕ k :=
  completedExteriorWedge (LaurentField κ r) ℕ k
    (fun i : Fin k => unitVector κ r (k * j + i.val + 1))

/-- The constant `M_r = max_{l ∈ ℕ} (l + 1) r^l` (the maximum exists, so it equals the
supremum). -/
def weightMax : ℝ := ⨆ l : ℕ, ((l : ℝ) + 1) * (r : ℝ) ^ l

/-- Proposition E.1: every block wedge has norm one. -/
theorem norm_blockWedge (hk : 2 ≤ k) (j : ℕ) : ‖blockWedge κ r k j‖ = 1 := by
  sorry

/-- Proposition E.1: `N / M_r ≤ ‖∑_{j<N} ω_j‖_B ≤ N` for `N ≥ 1`. -/
theorem blockWedge_sum_bounds (hk : 2 ≤ k) (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) / weightMax r ≤ ‖∑ j ∈ Finset.range N, blockWedge κ r k j‖ ∧
      ‖∑ j ∈ Finset.range N, blockWedge κ r k j‖ ≤ (N : ℝ) := by
  sorry

/-- Proposition E.1: the norm of `B` is not nonarchimedean. -/
theorem not_isUltrametricDist_B (hk : 2 ≤ k) :
    ¬ IsUltrametricDist (ProjectiveExteriorCompletion (LaurentField κ r) ℕ k) := by
  sorry

/-- Proposition E.1: `B` admits no equivalent nonarchimedean norm (over `K₁`). -/
theorem not_hasEquivalentUltrametricNorm_B (hk : 2 ≤ k) :
    ¬ HasEquivalentUltrametricNorm (LaurentField κ r)
      (ProjectiveExteriorCompletion (LaurentField κ r) ℕ k) := by
  sorry

/-- Proposition E.1: for `K' ⊇ K₁` satisfying (H1) and (H2), the norm of
`F = B ⊗̂_π K'` is not nonarchimedean. -/
theorem not_isUltrametricDist_F (hk : 2 ≤ k)
    (K' : Type u) [NontriviallyNormedField K'] [NormedAlgebra (LaurentField κ r) K']
    [IsUltrametricDist K'] :
    ¬ IsUltrametricDist (CompletedBaseChange (LaurentField κ r)
      (ProjectiveExteriorCompletion (LaurentField κ r) ℕ k) K') := by
  sorry

/-- Proposition E.1: for `K' ⊇ K₁` satisfying (H1) and (H2), `F = B ⊗̂_π K'` admits no
equivalent nonarchimedean norm, whether regarded as a normed space over `K'` or over any
subfield `K₀` of `K'`. -/
theorem not_hasEquivalentUltrametricNorm_F (hk : 2 ≤ k)
    (K' : Type u) [NontriviallyNormedField K'] [NormedAlgebra (LaurentField κ r) K']
    [IsUltrametricDist K']
    (K₀ : Type*) [NormedField K₀] [NormedAlgebra K₀ K']
    [NormedSpace K₀ (CompletedBaseChange (LaurentField κ r)
      (ProjectiveExteriorCompletion (LaurentField κ r) ℕ k) K')]
    [IsScalarTower K₀ K' (CompletedBaseChange (LaurentField κ r)
      (ProjectiveExteriorCompletion (LaurentField κ r) ℕ k) K')] :
    ¬ HasEquivalentUltrametricNorm K₀ (CompletedBaseChange (LaurentField κ r)
      (ProjectiveExteriorCompletion (LaurentField κ r) ℕ k) K') := by
  sorry

end AlternatingAnalyticChallenge.PropE_1
