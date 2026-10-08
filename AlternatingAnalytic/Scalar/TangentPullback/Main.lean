import AlternatingAnalytic.Scalar.TangentPullback.Charts
import AlternatingAnalytic.Scalar.TangentPullback.Pullback
import Mathlib.Analysis.Normed.Group.Ultra

/-!
# Proposition 6.5 from the scalar operator obstruction

Proposition 6.5 (tangent and pullback obstructions) follows from Theorem 6.1(2): Banach spaces
`E`, `D` for which scalar precomposition `A^k_{E,D;K}` is analytic at no point. The two
theorems below take such spaces as a hypothesis, stated exactly as the conclusion of
Theorem 6.1(2), and produce the two global charts of part (1) and the pullback of part (2).
-/

noncomputable section

namespace AlternatingAnalytic.TangentPullback

universe u

/-- **Proposition 6.5(1)**, from witnesses of Theorem 6.1(2): two global analytic charts `id`
and `ψ` on a Banach space whose induced transitions on scalar alternating `k`-forms are
analytic at no point. -/
theorem tangent_obstruction_of_scalar_obstruction (K : Type u) [NontriviallyNormedField K]
    [CompleteSpace K] (k : ℕ)
    (hobs : ∃ (E D : Type u) (_ : NormedAddCommGroup E) (_ : NormedSpace K E)
      (_ : CompleteSpace E) (_ : IsUltrametricDist E)
      (_ : NormedAddCommGroup D) (_ : NormedSpace K D) (_ : CompleteSpace D)
      (_ : IsUltrametricDist D),
      ∀ u₀ : E →L[K] D,
        ¬ AnalyticAt K
          (fun u : E →L[K] D =>
            (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
              (D [⋀^Fin k]→L[K] K) →L[K] (E [⋀^Fin k]→L[K] K))) u₀) :
    ∃ (X : Type u) (_ : NormedAddCommGroup X) (_ : NormedSpace K X) (_ : CompleteSpace X)
      (ψ : X ≃ X),
      AnalyticOnNhd K ψ Set.univ ∧ AnalyticOnNhd K ψ.symm Set.univ ∧
      (∀ x : X, ¬ AnalyticAt K
        (fun y : X => (ContinuousAlternatingMap.compContinuousLinearMapCLM (fderiv K ψ y) :
          (X [⋀^Fin k]→L[K] K) →L[K] (X [⋀^Fin k]→L[K] K))) x) ∧
      (∀ x : X, ¬ AnalyticAt K
        (fun y : X => (ContinuousAlternatingMap.compContinuousLinearMapCLM (fderiv K ψ.symm y) :
          (X [⋀^Fin k]→L[K] K) →L[K] (X [⋀^Fin k]→L[K] K))) x) := by
  obtain ⟨E, D, _, _, _, _, _, _, _, _, hA⟩ := hobs
  exact ⟨ChartSpace K D E, inferInstance, inferInstance, inferInstance, chartShear K D E,
    cpolynomialOn_chartShear.analyticOnNhd, cpolynomialOn_chartShear_symm.analyticOnNhd,
    not_analyticAt_chartShear_pullback hA, not_analyticAt_chartShear_symm_pullback hA⟩

/-- **Proposition 6.5(2)**, from witnesses of Theorem 6.1(2): a polynomial map `h` and an
analytic scalar `k`-form `ω₀` whose pullback is analytic at no point as an alternating-valued
map, but analytic everywhere as a multilinear-valued map. -/
theorem pullback_obstruction_of_scalar_obstruction (K : Type u) [NontriviallyNormedField K]
    [CompleteSpace K] (k : ℕ)
    (hobs : ∃ (E D : Type u) (_ : NormedAddCommGroup E) (_ : NormedSpace K E)
      (_ : CompleteSpace E) (_ : IsUltrametricDist E)
      (_ : NormedAddCommGroup D) (_ : NormedSpace K D) (_ : CompleteSpace D)
      (_ : IsUltrametricDist D),
      ∀ u₀ : E →L[K] D,
        ¬ AnalyticAt K
          (fun u : E →L[K] D =>
            (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
              (D [⋀^Fin k]→L[K] K) →L[K] (E [⋀^Fin k]→L[K] K))) u₀) :
    ∃ (N : Type u) (_ : NormedAddCommGroup N) (_ : NormedSpace K N) (_ : CompleteSpace N)
      (Y : Type u) (_ : NormedAddCommGroup Y) (_ : NormedSpace K Y) (_ : CompleteSpace Y)
      (h : N → Y) (ω₀ : Y → Y [⋀^Fin k]→L[K] K),
      CPolynomialOn K h Set.univ ∧ AnalyticOnNhd K ω₀ Set.univ ∧
      (∀ x : N, ¬ AnalyticAt K
        (fun y : N => (ω₀ (h y)).compContinuousLinearMap (fderiv K h y)) x) ∧
      AnalyticOnNhd K
        (fun y : N => ((ω₀ (h y)).compContinuousLinearMap (fderiv K h y)).toContinuousMultilinearMap)
        Set.univ := by
  obtain ⟨E, D, _, _, _, _, _, _, _, _, hA⟩ := hobs
  exact ⟨PullSource K D E K (Fin k), inferInstance, inferInstance, inferInstance,
    PullTarget K D K (Fin k), inferInstance, inferInstance, inferInstance,
    pullMap K D E K (Fin k), pullForm K D K (Fin k),
    cpolynomialOn_pullMap, analyticOnNhd_pullForm, not_analyticAt_pulledForm hA,
    analyticOnNhd_pulledForm_toContinuousMultilinearMap⟩

end AlternatingAnalytic.TangentPullback
