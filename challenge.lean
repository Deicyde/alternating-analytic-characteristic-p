import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Topology.VectorBundle.ContinuousAlternatingMap

/-!
Four challenges about continuous alternating maps and their vector bundles.
The first three concern precomposition `f ↦ (m ↦ m ∘ (f, …, f))`.
The first two refute universal `C^ω` regularity: first over all fields and normed
spaces, then over any prescribed positive-characteristic field in degree at least
its characteristic, using Banach spaces with `E' = E`.
The third is Theorem A: a spherically complete ultrametric target gives `C^n`
precomposition for every regularity order, including `ω`.
The fourth gives the actual analytic alternating-map bundle over an analytic base
with supplied finite continuous linear coordinates, in every characteristic and degree.

The named Banach and spherical-completeness assumptions below are defined directly
in Mathlib terms. All four proofs are intentional challenge placeholders.
-/

open scoped ContDiff

namespace AlternatingAnalyticChallenge

universe u uK uE uE' uF uι uS

/-- Assume that precomposition on continuous alternating maps is `C^ω` for all
nontrivially normed fields, all normed spaces, and all finite index types. Then `False`. -/
theorem false_of_contDiff_omega_compContinuousLinearMapCLM
    (h : ∀ (𝕜 : Type) [NontriviallyNormedField 𝕜] (E E' F : Type)
      [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
      [NormedAddCommGroup F] [NormedSpace 𝕜 F] (ι : Type) [Fintype ι],
      ContDiff 𝕜 ω
        (fun f : E →L[𝕜] E' =>
          (ContinuousAlternatingMap.compContinuousLinearMapCLM f :
            (E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)))) : False := by
  sorry

/-- Precomposition on degree-`k` continuous alternating maps is `C^ω` for every
pair of Banach spaces over `K`, with `E' = E` and index `Fin k`.
The field `K` itself need not be complete. -/
def BanachPrecompositionAnalytic
    (K : Type u) [NontriviallyNormedField K] (k : ℕ) : Prop :=
  ∀ (E F : Type u) [NormedAddCommGroup E] [NormedSpace K E] [CompleteSpace E]
      [NormedAddCommGroup F] [NormedSpace K F] [CompleteSpace F],
      ContDiff K ω
        (fun f : E →L[K] E =>
          (ContinuousAlternatingMap.compContinuousLinearMapCLM f :
            (E [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F)))

/-- For any prescribed nontrivially normed field of characteristic `p` and any
`k ≥ p`, assume `C^ω` precomposition for all Banach spaces with `E' = E` and index
`Fin k`. Then `False`. The field need not be complete. -/
theorem false_of_contDiff_omega_compContinuousLinearMapCLM_charP_banach
    (K : Type u) [NontriviallyNormedField K] (p k : ℕ) (hp : p.Prime)
    [CharP K p] (hpk : p ≤ k)
    (h : BanachPrecompositionAnalytic K k) : False := by
  sorry

/-- Every nonempty family of pairwise-intersecting closed balls has a common point.
This is the spherical-completeness hypothesis in Theorem A. -/
def SphericallyComplete (F : Type uS) [PseudoMetricSpace F] : Prop :=
  ∀ S : Set (F × ℝ), S.Nonempty →
    (∀ p ∈ S, ∀ q ∈ S,
      (Metric.closedBall p.1 p.2 ∩ Metric.closedBall q.1 q.2).Nonempty) →
    (⋂ p ∈ S, Metric.closedBall p.1 p.2).Nonempty

/-- **Theorem A.** A spherically complete ultrametric target makes alternating
precomposition `C^n` for every order `n`, including analytic regularity `ω`.
There is no restriction on the characteristic or finite degree. Neither `K`, `E`
nor `E'` is assumed complete, and the norms on `E` and `E'` need not be ultrametric. -/
theorem contDiff_compContinuousLinearMapCLM_of_sphericallyComplete
    (K : Type uK) [NontriviallyNormedField K] [IsUltrametricDist K]
    (E : Type uE) (E' : Type uE') (F : Type uF)
    [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup E'] [NormedSpace K E']
    [NormedAddCommGroup F] [NormedSpace K F] [IsUltrametricDist F]
    (ι : Type uι) [Fintype ι]
    (hF : SphericallyComplete F) (n : WithTop ℕ∞) :
    ContDiff K n
      (fun f : E →L[K] E' =>
        (ContinuousAlternatingMap.compContinuousLinearMapCLM f :
          (E' [⋀^ι]→L[K] F) →L[K] (E [⋀^ι]→L[K] F))) := by
  sorry

section AnalyticAlternatingBundle

open Bundle
open scoped Bundle Manifold

/-- The alternating-map bundle of two analytic normed vector bundles is itself
analytic when the base has supplied finite continuous linear coordinates.
This uses Mathlib's existing topology on the actual alternating-map fibers.
The field and model fibers need not be complete; every characteristic and every
base dimension `d` and alternating degree `k`, including zero, are allowed. -/
theorem contMDiffVectorBundle_alternating_of_finiteCoordinates
    {K M F₁ F₂ : Type*} [NontriviallyNormedField K] [TopologicalSpace M]
    [NormedAddCommGroup F₁] [NormedSpace K F₁]
    [NormedAddCommGroup F₂] [NormedSpace K F₂]
    {E₁ E₂ : M → Type*}
    [∀ x, AddCommGroup (E₁ x)] [∀ x, Module K (E₁ x)]
    [∀ x, AddCommGroup (E₂ x)] [∀ x, Module K (E₂ x)]
    [TopologicalSpace (TotalSpace F₁ E₁)] [TopologicalSpace (TotalSpace F₂ E₂)]
    [∀ x, TopologicalSpace (E₁ x)] [∀ x, TopologicalSpace (E₂ x)]
    [FiberBundle F₁ E₁] [VectorBundle K F₁ E₁]
    [FiberBundle F₂ E₂] [VectorBundle K F₂ E₂]
    [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul K (E₂ x)]
    {P : Type*} [NormedAddCommGroup P] [NormedSpace K P]
    [ChartedSpace P M] [IsManifold 𝓘(K, P) ω M]
    [ContMDiffVectorBundle ω F₁ E₁ 𝓘(K, P)]
    [ContMDiffVectorBundle ω F₂ E₂ 𝓘(K, P)]
    {d : ℕ} (c : P ≃L[K] (Fin d → K)) (k : ℕ) :
    ContMDiffVectorBundle ω (F₁ [⋀^Fin k]→L[K] F₂)
      (fun x ↦ E₁ x [⋀^Fin k]→L[K] E₂ x) 𝓘(K, P) := by
  sorry

end AnalyticAlternatingBundle

end AlternatingAnalyticChallenge
