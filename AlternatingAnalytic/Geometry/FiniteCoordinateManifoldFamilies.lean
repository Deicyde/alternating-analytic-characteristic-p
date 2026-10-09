import AlternatingAnalytic.Analysis.FiniteCoordinateFamilies
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# The alternating action on analytic families over finite-coordinate manifolds

On an open subset of an analytic manifold whose model has continuous linear coordinates
`P ≃L[K] K^d`, the model action `alternatingMapAction` takes analytic families
`γ = (u, v)` to analytic families. This is the finite-coordinate input to Corollary 4.6,
from Theorem 4.4 via `isAdmissibleOn_of_finite_coordinates`. Neither the field nor the fibers
need be complete.
-/

noncomputable section

open scoped Manifold ContDiff
open Set

namespace AlternatingAnalytic

variable {K P M E E' F F' : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup P] [NormedSpace K P]
  [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup E'] [NormedSpace K E']
  [NormedAddCommGroup F] [NormedSpace K F]
  [NormedAddCommGroup F'] [NormedSpace K F']

/-- On an open subset of a finite-coordinate space, the alternating action preserves
`C^ω` families. -/
theorem contDiffOn_alternatingMapAction_of_finiteCoordinates {d : ℕ}
    (c : P ≃L[K] (Fin d → K)) (k : ℕ)
    {U : Set P} (hU : IsOpen U)
    {γ : P → (E' →L[K] E) × (F →L[K] F')}
    (hγ : ContDiffOn K ω γ U) :
    ContDiffOn K ω (alternatingMapAction k ∘ γ) U := by
  have hγa : AnalyticOnNhd K γ U :=
    hU.analyticOn_iff_analyticOnNhd.mp
      ((contDiffOn_omega_iff_analyticOn hU.uniqueDiffOn).mp hγ)
  exact (isAdmissibleOn_of_finite_coordinates c k hγa).2.contDiffOn hU.uniqueDiffOn

variable [TopologicalSpace M] [ChartedSpace P M] [IsManifold 𝓘(K, P) ω M]

/-- In every chart, an analytic family on `U` is admissible on the chart domain over `U`. -/
theorem isAdmissibleOn_extChartAt_of_finiteCoordinates {d : ℕ}
    (c : P ≃L[K] (Fin d → K)) (k : ℕ)
    {U : Set M} (hU : IsOpen U)
    {γ : M → (E' →L[K] E) × (F →L[K] F')}
    (hγ : ContMDiffOn 𝓘(K, P)
      𝓘(K, (E' →L[K] E) × (F →L[K] F')) ω γ U) (x : M) :
    IsAdmissibleOn k (γ ∘ (extChartAt 𝓘(K, P) x).symm)
      ((extChartAt 𝓘(K, P) x).target ∩ (extChartAt 𝓘(K, P) x).symm ⁻¹' U) := by
  have hV : IsOpen ((extChartAt 𝓘(K, P) x).target ∩
      (extChartAt 𝓘(K, P) x).symm ⁻¹' U) :=
    (continuousOn_extChartAt_symm x).isOpen_inter_preimage
      (isOpen_extChartAt_target x) hU
  have hγc : ContDiffOn K ω (γ ∘ (extChartAt 𝓘(K, P) x).symm)
      ((extChartAt 𝓘(K, P) x).target ∩ (extChartAt 𝓘(K, P) x).symm ⁻¹' U) := by
    simpa [chartAt_self_eq, mfld_simps] using (contMDiffOn_iff.mp hγ).2 x 0
  exact isAdmissibleOn_of_finite_coordinates c k
    (hV.analyticOn_iff_analyticOnNhd.mp
      ((contDiffOn_omega_iff_analyticOn hV.uniqueDiffOn).mp hγc))

/-- Over a finite-coordinate analytic manifold, the alternating action preserves analytic
families on open sets. -/
theorem contMDiffOn_alternatingMapAction_of_finiteCoordinates {d : ℕ}
    (c : P ≃L[K] (Fin d → K)) (k : ℕ)
    {U : Set M} (hU : IsOpen U)
    {γ : M → (E' →L[K] E) × (F →L[K] F')}
    (hγ : ContMDiffOn 𝓘(K, P)
      𝓘(K, (E' →L[K] E) × (F →L[K] F')) ω γ U) :
    ContMDiffOn 𝓘(K, P)
      𝓘(K, (E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F'))
      ω (alternatingMapAction k ∘ γ) U := by
  intro x hx
  have hV : IsOpen ((extChartAt 𝓘(K, P) x).target ∩
      (extChartAt 𝓘(K, P) x).symm ⁻¹' U) :=
    (continuousOn_extChartAt_symm x).isOpen_inter_preimage
      (isOpen_extChartAt_target x) hU
  have hxV : extChartAt 𝓘(K, P) x x ∈
      (extChartAt 𝓘(K, P) x).target ∩ (extChartAt 𝓘(K, P) x).symm ⁻¹' U := by
    simpa only [mfld_simps] using hx
  have ha := (isAdmissibleOn_extChartAt_of_finiteCoordinates c k hU hγ x).2
  have hc : ContMDiffOn 𝓘(K, P)
      𝓘(K, (E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F'))
      ω ((alternatingMapAction k ∘ γ) ∘ (extChartAt 𝓘(K, P) x).symm)
      ((extChartAt 𝓘(K, P) x).target ∩ (extChartAt 𝓘(K, P) x).symm ⁻¹' U) :=
    contMDiffOn_iff_contDiffOn.mpr (ha.contDiffOn hV.uniqueDiffOn)
  apply ContMDiffAt.contMDiffWithinAt
  apply contMDiffAt_iff_source.mpr
  exact (hc.contMDiffAt (hV.mem_nhds hxV)).contMDiffWithinAt

/-- Over a finite-coordinate analytic manifold, the alternating action preserves analytic
families. -/
theorem contMDiff_alternatingMapAction_of_finiteCoordinates {d : ℕ}
    (c : P ≃L[K] (Fin d → K)) (k : ℕ)
    {γ : M → (E' →L[K] E) × (F →L[K] F')}
    (hγ : ContMDiff 𝓘(K, P)
      𝓘(K, (E' →L[K] E) × (F →L[K] F')) ω γ) :
    ContMDiff 𝓘(K, P)
      𝓘(K, (E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F'))
      ω (alternatingMapAction k ∘ γ) := by
  rw [← contMDiffOn_univ]
  exact contMDiffOn_alternatingMapAction_of_finiteCoordinates c k isOpen_univ
    hγ.contMDiffOn

end AlternatingAnalytic
