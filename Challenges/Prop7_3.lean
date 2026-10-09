import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Topology.VectorBundle.ContinuousAlternatingMap

/-!
# Proposition 7.3 (comparison with alternating-bundle sections), p. 19

Setting (Section 7): `K` complete and nontrivially normed, manifold models arbitrary normed
spaces, `C^ω` charts; an ambient analytic form is one whose chart representatives are analytic
after the inclusion `j : Alt^k(P; K) ↪ Mult^k(P; K)` (Definition 7.1).

Paper statement: Every intrinsically analytic alternating-valued coefficient map is ambient
analytic. If, for the model space `P`, the inclusion `j` has a bounded linear retraction, then
the natural alternating cotangent atlas is analytic and its analytic sections are precisely the
ambient analytic forms. The same conclusion holds when `P` has finite continuous coordinates.

## Formalization notes
* The degree is `Fin k`; `[CompleteSpace K]` as in Section 7.
* Chart level: a coefficient map on an open `U ⊆ P` is `η : P → Alt^k(P; K)`. "Intrinsically
  analytic" is `AnalyticOnNhd K η U`; "ambient analytic" is `IsAmbientAnalyticOn η U`, i.e.
  `AnalyticOnNhd K (j ∘ η) U` with `j = ContinuousAlternatingMap.toContinuousMultilinearMap`
  (as in `Challenges/Thm7_2.lean`).
* "The alternating cotangent atlas is analytic" is stated in a chart: for every `C^ω` map `ψ`
  on an open `U ⊆ P`, the transition `y ↦ (Dψ(y))^*` on `Alt^k(P; K)` is analytic on `U`. This
  covers all `C^ω` maps, not only invertible ones. "Its analytic sections are the ambient
  analytic forms" is `AnalyticOnNhd K η U ↔ IsAmbientAnalyticOn η U`.
* Manifold level: `part2_manifold` and `part3_manifold` state the atlas claim for an analytic
  manifold `M` modeled on `P`: Mathlib's bundle `x ↦ Alt^k(T_x M; K)` is
  `ContMDiffVectorBundle ω`. The section statement on `M` is not formalized (Mathlib has no
  bundle of continuous multilinear maps to express ambient forms on `M`).
* A bounded linear retraction of `j` is `R : Mult^k(P; K) →L[K] Alt^k(P; K)` with
  `R (j a) = a`. Finite continuous coordinates are `c : P ≃L[K] (Fin d → K)`.
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

/-- Proposition 7.3, part 1: intrinsically analytic coefficient maps are ambient analytic. -/
theorem part1 (k : ℕ) (U : Set P) (η : P → P [⋀^Fin k]→L[K] K) (hη : AnalyticOnNhd K η U) :
    IsAmbientAnalyticOn η U := by
  sorry

/-- Proposition 7.3, part 2, in a chart: if `j` has a bounded linear retraction, then the
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
      (AnalyticOnNhd K η U ↔ IsAmbientAnalyticOn η U)) := by
  sorry

/-- Proposition 7.3, part 3, in a chart: the same conclusions when `P` has finite
continuous coordinates. -/
theorem part3 (k : ℕ) {d : ℕ} (c : P ≃L[K] (Fin d → K)) :
    (∀ (U : Set P) (ψ : P → P), IsOpen U → ContDiffOn K ω ψ U →
      AnalyticOnNhd K
        (fun y => (ContinuousAlternatingMap.compContinuousLinearMapCLM (fderiv K ψ y) :
          (P [⋀^Fin k]→L[K] K) →L[K] (P [⋀^Fin k]→L[K] K))) U) ∧
    (∀ (U : Set P) (η : P → P [⋀^Fin k]→L[K] K), IsOpen U →
      (AnalyticOnNhd K η U ↔ IsAmbientAnalyticOn η U)) := by
  sorry

/-- Proposition 7.3, part 2, atlas on a manifold: if `j` has a bounded linear retraction,
the alternating cotangent bundle `x ↦ Alt^k(T_x M; K)` of an analytic manifold modeled on `P`
is an analytic vector bundle. -/
theorem part2_manifold (k : ℕ)
    (R : ContinuousMultilinearMap K (fun _ : Fin k => P) K →L[K] (P [⋀^Fin k]→L[K] K))
    (hR : ∀ a : P [⋀^Fin k]→L[K] K, R a.toContinuousMultilinearMap = a)
    (M : Type uM) [TopologicalSpace M] [ChartedSpace P M] [IsManifold 𝓘(K, P) ω M] :
    ContMDiffVectorBundle ω (P [⋀^Fin k]→L[K] K)
      (fun x : M => TangentSpace 𝓘(K, P) x [⋀^Fin k]→L[K] Bundle.Trivial M K x) 𝓘(K, P) := by
  sorry

/-- Proposition 7.3, part 3, atlas on a manifold: with finite continuous coordinates on
`P`, the alternating cotangent bundle of an analytic manifold modeled on `P` is analytic. -/
theorem part3_manifold (k : ℕ) {d : ℕ} (c : P ≃L[K] (Fin d → K))
    (M : Type uM) [TopologicalSpace M] [ChartedSpace P M] [IsManifold 𝓘(K, P) ω M] :
    ContMDiffVectorBundle ω (P [⋀^Fin k]→L[K] K)
      (fun x : M => TangentSpace 𝓘(K, P) x [⋀^Fin k]→L[K] Bundle.Trivial M K x) 𝓘(K, P) := by
  sorry

end AlternatingAnalyticChallenge.Prop7_3
