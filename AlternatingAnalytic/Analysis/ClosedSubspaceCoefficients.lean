import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-! Diagonal Taylor coefficients of a map locally valued in a closed subspace. -/

noncomputable section

open Filter
open scoped Topology

namespace AlternatingAnalytic

variable {K E Z : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup Z] [NormedSpace K Z]

/-- Closed subspaces contain the diagonal coefficients of an ambient analytic expansion
whose represented map locally takes values in that subspace. No completeness is needed. -/
theorem HasFPowerSeriesAt.diagonal_mem_closedSubspace
    (W : Submodule K Z) (hW : IsClosed (W : Set Z))
    {p : FormalMultilinearSeries K E Z} {f : E → Z} {x : E}
    (hf : HasFPowerSeriesAt f p x) (hmem : ∀ᶠ y in 𝓝 x, f y ∈ W)
    (n : ℕ) (y : E) : p n (fun _ => y) ∈ W := by
  let : IsClosed (W : Set Z) := hW
  have hq : HasFPowerSeriesAt (W.mkQL ∘ f) (W.mkQL.compFormalMultilinearSeries p) x := by
    obtain ⟨r, hr⟩ := hf
    exact ⟨r, W.mkQL.comp_hasFPowerSeriesOnBall hr⟩
  have hz : W.mkQL ∘ f =ᶠ[𝓝 x] 0 := by
    filter_upwards [hmem] with z hz
    simpa using (Submodule.Quotient.mk_eq_zero W).mpr hz
  have hcoeff := (hq.congr hz).apply_eq_zero n y
  exact (Submodule.Quotient.mk_eq_zero W).mp hcoeff

end AlternatingAnalytic
