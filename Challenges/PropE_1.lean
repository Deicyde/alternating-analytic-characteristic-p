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

* `K₁` is the library's `LaurentField κ r` (`LaurentSeries κ` with `‖a‖ = r^{ord a}`), with
  `r : ℝ≥0`, `Fact (0 < r)`, `Fact (r < 1)`. `E₁ = ℕ →ᵇ K₁`.
* `B` is `ProjectiveExteriorCompletion K₁ ℕ k`, the completion of `⋀[K₁]^k (ℕ →ᵇ K₁)` under the
  projective exterior norm; the wedge is `completedExteriorWedge`. The inclusion `κ^ℕ → E₁` is
  `constantLaurentArray`, and `F = B ⊗̂_π K'` is `CompletedBaseChange`.
* Defined here: `unitVector n = e_n`, `blockWedge j = ω_j`, `weightMax r = M_r` (as a supremum,
  which is attained). Indices start at `0`; the blocks use `kj + 1, …, kj + k` as in the paper,
  so index `0` is unused.
* "Equivalent nonarchimedean norm" is `HasEquivalentUltrametricNorm K F`: an ultrametric
  `K`-seminorm bounded above and below by positive multiples of `‖·‖`. "The norm is not
  nonarchimedean" is `¬ IsUltrametricDist`.
* (H1) holds automatically for `K₁`; (H2) is `[IsUltrametricDist K']`, and `K₁ ⊆ K'` is
  `[NormedAlgebra K₁ K']`. `K'` lives in the universe of `κ`.
* "Over any subfield `K₀` of `K'`" is a normed field `K₀` with `[NormedAlgebra K₀ K']` and
  `IsScalarTower K₀ K' F`; this includes `K₀ = K'`.
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
      (ProjectiveExteriorCompletion (LaurentField κ r) ℕ k) K') := by
  sorry

end AlternatingAnalyticChallenge.PropE_1
