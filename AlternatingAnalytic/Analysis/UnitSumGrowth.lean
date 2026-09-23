import AlternatingAnalytic.Analysis.EquivalentUltrametric
import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-! Scalar-independent unit-sum growth and its preservation by isometric embeddings. -/

namespace AlternatingAnalytic

/-- Unit vectors with linearly growing partial sums. This property depends only
on the additive norm, so survives restriction to a dense scalar field. -/
def HasLinearUnitSumGrowth (F : Type*) [NormedAddCommGroup F] : Prop :=
  ∃ (v : ℕ → F) (M : ℝ), 0 < M ∧ (∀ j, ‖v j‖ ≤ 1) ∧
    ∀ N : ℕ, (N : ℝ) / M ≤ ‖∑ i ∈ Finset.range N, v i‖

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

/-- The same unit wedges and growth estimates persist under any additive isometry. -/
theorem HasLinearUnitSumGrowth.map (h : HasLinearUnitSumGrowth E)
    (i : E →+ F) (hi : Isometry i) : HasLinearUnitSumGrowth F := by
  obtain ⟨v, M, hM, hv, hgrowth⟩ := h
  have hn (x : E) : ‖i x‖ = ‖x‖ := hi.norm_map_of_map_zero i.map_zero x
  refine ⟨i ∘ v, M, hM, fun j => ?_, fun N => ?_⟩
  · simpa only [Function.comp_apply, hn] using hv j
  · simpa only [Function.comp_apply, ← map_sum, hn] using hgrowth N

/-- Unit-sum growth forbids an equivalent ultrametric norm over every scalar field
that acts as a normed space on the given additive group. -/
theorem HasLinearUnitSumGrowth.not_hasEquivalentUltrametricNorm
    (h : HasLinearUnitSumGrowth F) (K : Type*) [NormedField K] [NormedSpace K F] :
    ¬ HasEquivalentUltrametricNorm K F := by
  obtain ⟨v, M, hM, hv, hgrowth⟩ := h
  exact not_hasEquivalentUltrametricNorm_of_linear_growth v hv hM hgrowth

end AlternatingAnalytic
