import AlternatingAnalytic.Analysis.FiniteCoordinateFamilies
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Finite-coordinate manifold families of alternating-map actions

On an open subset of an analytic manifold with specified continuous linear
coordinates in `K^d`, an analytic operator family induces an analytic family
of operators on continuous alternating maps. The first input is contravariant.

The proof works on whole open chart domains: it converts `C^ω` to ordinary
analyticity, applies finite-coordinate admissibility, and converts back using
unique differentiability of the open domain. Neither the field nor the fibers
are assumed complete; the dimensions and the alternating degree may be zero.

This is the local manifold-family prerequisite in the proof of
`paper/charp.tex`, `fam:thm:finite-bundles`, not the bundle construction or the
category-theoretic bifunctor assertion itself.
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

/-- On an open finite-coordinate parameter domain, the alternating action
preserves `C^ω` without completeness assumptions. -/
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

/-- In every base chart, an analytic manifold family is admissible on the
entire open chart domain lying over `U`. -/
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

/-- The alternating action preserves analytic operator-valued families on
open subsets of manifolds with supplied finite continuous linear coordinates. -/
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

/-- Global analytic families induce global analytic alternating-map actions. -/
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
