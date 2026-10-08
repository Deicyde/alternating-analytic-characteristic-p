import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Topology.VectorBundle.ContinuousAlternatingMap
import AlternatingAnalytic.Forms.Comparison.Bundle

/-!
# Proposition 7.3 (comparison with alternating-bundle sections), p. 19

Solution: the statements of `Challenges/Prop7_3.lean`, proved from the library:
* part 1: `AlternatingAnalytic.analyticOnNhd_toContinuousMultilinearMap`
  (`Forms/Comparison/Basic.lean`), composition with `j`;
* part 2 (chart level): `analyticOnNhd_compContinuousLinearMapCLM_fderiv_of_retraction` and
  `analyticOnNhd_iff_toContinuousMultilinearMap_of_retraction` (`Forms/Comparison/Basic.lean`);
* part 3 (chart level): `analyticOnNhd_compContinuousLinearMapCLM_fderiv_of_finiteCoordinates` and
  `analyticOnNhd_iff_toContinuousMultilinearMap_of_finiteCoordinates`
  (`Forms/Comparison/Basic.lean`, via the finite-coordinate reflection theorem);
* part 2 (manifold level): `contMDiffVectorBundle_alternating_of_retraction`
  (`Forms/Comparison/Bundle.lean`);
* part 3 (manifold level): `contMDiffVectorBundle_alternating_of_finiteCoordinates`
  (`Geometry/AnalyticAlternatingBundle.lean`).
-/

open scoped ContDiff Manifold

namespace AlternatingAnalyticChallenge.Prop7_3

universe uK uP uM

/-- Ambient analyticity of a `k`-form `η` on `U`: `j ∘ η` is analytic on `U`. -/
def IsAmbientAnalyticOn {K : Type uK} [NontriviallyNormedField K]
    {P : Type uP} [NormedAddCommGroup P] [NormedSpace K P] {k : ℕ}
    (η : P → P [⋀^Fin k]→L[K] K) (U : Set P) : Prop :=
  AnalyticOnNhd K (fun y => (η y).toContinuousMultilinearMap) U

variable (K : Type uK) [NontriviallyNormedField K] [CompleteSpace K]
  (P : Type uP) [NormedAddCommGroup P] [NormedSpace K P]

/-- **Proposition 7.3, part 1.** Intrinsically analytic coefficient maps are ambient analytic. -/
theorem part1 (k : ℕ) (U : Set P) (η : P → P [⋀^Fin k]→L[K] K) (hη : AnalyticOnNhd K η U) :
    IsAmbientAnalyticOn η U :=
  AlternatingAnalytic.analyticOnNhd_toContinuousMultilinearMap hη

/-- **Proposition 7.3, part 2 (chart level).** If `j` has a bounded linear retraction, then the
induced alternating transitions of `C^ω` chart changes are analytic, and intrinsic and ambient
analyticity of coefficient maps coincide. -/
theorem part2 (k : ℕ)
    (R : ContinuousMultilinearMap K (fun _ : Fin k => P) K →L[K] (P [⋀^Fin k]→L[K] K))
    (hR : ∀ a : P [⋀^Fin k]→L[K] K, R a.toContinuousMultilinearMap = a) :
    (∀ (U : Set P) (ψ : P → P), IsOpen U → ContDiffOn K ω ψ U →
      AnalyticOnNhd K
        (fun y => (ContinuousAlternatingMap.compContinuousLinearMapCLM (fderiv K ψ y) :
          (P [⋀^Fin k]→L[K] K) →L[K] (P [⋀^Fin k]→L[K] K))) U) ∧
    (∀ (U : Set P) (η : P → P [⋀^Fin k]→L[K] K), IsOpen U →
      (AnalyticOnNhd K η U ↔ IsAmbientAnalyticOn η U)) :=
  ⟨fun _ _ hU hψ =>
    AlternatingAnalytic.analyticOnNhd_compContinuousLinearMapCLM_fderiv_of_retraction R hR hU hψ,
    fun U η _ =>
      AlternatingAnalytic.analyticOnNhd_iff_toContinuousMultilinearMap_of_retraction R hR U η⟩

/-- **Proposition 7.3, part 3 (chart level).** The same conclusions when `P` has finite
continuous coordinates. -/
theorem part3 (k : ℕ) {d : ℕ} (c : P ≃L[K] (Fin d → K)) :
    (∀ (U : Set P) (ψ : P → P), IsOpen U → ContDiffOn K ω ψ U →
      AnalyticOnNhd K
        (fun y => (ContinuousAlternatingMap.compContinuousLinearMapCLM (fderiv K ψ y) :
          (P [⋀^Fin k]→L[K] K) →L[K] (P [⋀^Fin k]→L[K] K))) U) ∧
    (∀ (U : Set P) (η : P → P [⋀^Fin k]→L[K] K), IsOpen U →
      (AnalyticOnNhd K η U ↔ IsAmbientAnalyticOn η U)) :=
  ⟨fun _ _ hU hψ =>
    AlternatingAnalytic.analyticOnNhd_compContinuousLinearMapCLM_fderiv_of_finiteCoordinates c hU
      hψ,
    fun U η _ =>
      AlternatingAnalytic.analyticOnNhd_iff_toContinuousMultilinearMap_of_finiteCoordinates c U η⟩

/-- **Proposition 7.3, part 2 (manifold level, atlas).** If `j` has a bounded linear retraction,
the alternating cotangent bundle `x ↦ Alt^k(T_x M; K)` of an analytic manifold modeled on `P`
is an analytic vector bundle. -/
theorem part2_manifold (k : ℕ)
    (R : ContinuousMultilinearMap K (fun _ : Fin k => P) K →L[K] (P [⋀^Fin k]→L[K] K))
    (hR : ∀ a : P [⋀^Fin k]→L[K] K, R a.toContinuousMultilinearMap = a)
    (M : Type uM) [TopologicalSpace M] [ChartedSpace P M] [IsManifold 𝓘(K, P) ω M] :
    ContMDiffVectorBundle ω (P [⋀^Fin k]→L[K] K)
      (fun x : M => TangentSpace 𝓘(K, P) x [⋀^Fin k]→L[K] Bundle.Trivial M K x) 𝓘(K, P) :=
  AlternatingAnalytic.contMDiffVectorBundle_alternating_of_retraction k R hR

/-- **Proposition 7.3, part 3 (manifold level, atlas).** With finite continuous coordinates on
`P`, the alternating cotangent bundle of an analytic manifold modeled on `P` is analytic. -/
theorem part3_manifold (k : ℕ) {d : ℕ} (c : P ≃L[K] (Fin d → K))
    (M : Type uM) [TopologicalSpace M] [ChartedSpace P M] [IsManifold 𝓘(K, P) ω M] :
    ContMDiffVectorBundle ω (P [⋀^Fin k]→L[K] K)
      (fun x : M => TangentSpace 𝓘(K, P) x [⋀^Fin k]→L[K] Bundle.Trivial M K x) 𝓘(K, P) :=
  AlternatingAnalytic.contMDiffVectorBundle_alternating_of_finiteCoordinates c k

end AlternatingAnalyticChallenge.Prop7_3
