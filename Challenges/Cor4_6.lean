import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Topology.VectorBundle.ContinuousAlternatingMap
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Module.Seminorm.Basic

/-!
# Corollary 4.6 (the bundle theorem), p. 12

Paper statement (Section 4.3, `cor:bundle-cases`): Let `M` be an analytic manifold over `K`, with
normed model space `P`. Fiberwise alternating maps give an analytic bifunctor on analytic normed
vector bundles and their operator-valued analytic morphisms in each of the following settings:

| Base model | Hypotheses on the typical fibers |
|---|---|
| Arbitrary `P` | `k! ≠ 0` in `K`; or `K` is nonarchimedean and the target fibers admit equivalent nonarchimedean spherically complete norms; or the source fibers have finite continuous coordinates. |
| Finite continuous coordinates | Arbitrary normed fibers. |
| `c₀(I, K)`, or a bounded linear retract | `K` nonarchimedean; complete nonarchimedean target fibers. |
| `ℓ¹(I, K)`, or a bounded linear retract | Complete target fibers. |

The fiber hypotheses apply to both pairs of bundles at the endpoints of a morphism. Each
alternative in the first row specifies a separate setting. At every finite smoothness order and
at `C^∞`, no additional hypothesis on `K`, `P` or the fibers is needed.

## Formalization notes
* One pair of theorems per setting (six settings: three alternatives of row 1, rows 2-4) plus a
  pair for the final `C^n`/`C^∞` sentence: `<setting>_bundle` (objects) and
  `<setting>_morphism` (morphisms). 14 theorems in all.
* Analytic manifold: `[ChartedSpace P M] [IsManifold 𝓘(K, P) ω M]` (open-chart model, no
  boundary or corners). Analytic normed vector bundle: Mathlib `FiberBundle` + `VectorBundle` +
  `ContMDiffVectorBundle ω _ _ 𝓘(K, P)` with normed model fiber; the actual fibers carry
  topological-vector-space instances.
* Object part: the bundle `x ↦ E₁ x [⋀^Fin k]→L[K] E₂ x` of continuous alternating maps, with
  Mathlib's existing topology and trivialization atlas, is `ContMDiffVectorBundle ω` with model
  fiber `F₁ [⋀^Fin k]→L[K] F₂`. Here `F₁` is the source and `F₂` the target typical fiber.
* Morphism part: an operator-valued analytic morphism is an analytic section of the Hom bundle
  (`ContMDiffSection 𝓘(K, P) (A' →L[K] A) ω (fun b ↦ E' b →L[K] E b)`, contravariant slot, and
  `v` likewise for `F → F'`, covariant slot). The conclusion is that the fiberwise map
  `m ↦ v ∘ m ∘ (u, …, u)` is an analytic section of the Hom bundle between the two alternating
  bundles. Source typical fibers are `A, A'`, target typical fibers `B, B'`; the fiber
  hypotheses are imposed on both pairs, as the paper says.
* "Bifunctor": the functor laws (identity and composition) are pointwise consequences of the
  fiber formula `T b m = v b ∘ m ∘ (u b, …, u b)` and are not stated separately. The library
  states them for the finite-coordinate row only (`alternatingBundleHom_of_finiteCoordinates_id`,
  `_comp`, `alternatingBundleFunctor`).
* Degree: index type `Fin k`, as in the library's bundle files.
* "Finite continuous coordinates" for a space `X` is a continuous linear equivalence
  `X ≃L[K] (Fin d → K)` (equivalently, a finite basis with continuous coordinate functionals).
* `k! ≠ 0` is `((k.factorial : ℕ) : K) ≠ 0`.
* "Nonarchimedean" for `K` and for target fibers in row 3 is `IsUltrametricDist` of the given
  norm; "complete" is `CompleteSpace`.
* Row 1, spherical alternative: "admit equivalent nonarchimedean spherically complete norms" is
  the definition `HasEquivalentSphericallyCompleteUltrametricNorm` introduced here: a seminorm
  `q` satisfying the strong triangle inequality, two-sided bounds against the given norm, and the
  spherical-completeness property for `q`-balls (every nonempty family of pairwise-intersecting
  closed `q`-balls has a common point). It is stated self-containedly. Cross-checked: its first
  three fields coincide with the library's `HasEquivalentUltrametricNorm`
  (`Analysis/EquivalentUltrametric.lean`), and its last clause is the library's
  `SphericallyCompleteSpace.inter_nonempty` (`Analysis/SphericalCompleteness.lean`) restated for
  `q`-balls; negative radii are excluded automatically, since the self-intersection condition
  forces `p.2 ≥ 0`.
* `c₀(I, K)` is `C₀(I, K)` for a discrete index type `I`; `ℓ¹(I, K)` is
  `lp (fun _ : I => K) 1`. "`P` is the space or a bounded linear retract of it" is stated as
  bounded linear `i : P → V`, `r : V → P`, `r ∘ i = id`, which includes `P = V`.
* The `C^n`/`C^∞` sentence: `n : ℕ∞` (finite orders and `∞`, not `ω`), `M` a `C^n` manifold,
  `C^n` bundles and `C^n` sections; no hypotheses on `K`, `P` or fibers.
* No completeness of `K`, `P` or the fibers beyond what the table states.

## Library status (per theorem); overall status: partially proved, no comparator solution
| Theorems | Status | Where |
|---|---|---|
| `row2_finiteCoordinateBase_bundle`, `row2_finiteCoordinateBase_morphism` | proved in the library, by `exact` | `contMDiffVectorBundle_alternating_of_finiteCoordinates` (`Geometry/AnalyticAlternatingBundle.lean`), `alternatingBundleHom_of_finiteCoordinates` (`Geometry/AnalyticAlternatingBundleMorphism.lean`) |
| `row1_factorial_*`, `row1_finiteSourceCoordinates_*`, `row3_c0Retract_*`, `row4_l1Retract_*`, `smooth_*` (10 theorems) | proved in `Partial/Cor4_6.lean` (library + glue), not library declarations | see below |
| `row1_spherical_bundle`, `row1_spherical_morphism` | not proved (`sorry` in `Partial/Cor4_6.lean`) | see below |

* `Partial/Cor4_6.lean` repeats the 14 statements of this file character for character and
  proves 12 of them; only the two `row1_spherical_*` theorems are `sorry`. It is a partial proof
  file, not a comparator solution: there is no `Solutions/Cor4_6.lean` and no `Cor4_6.json`.
* The 10 glue-proved theorems have no bundle-level statement in the library. Each is derived from
  the library's generic assemblies `contMDiffVectorBundle_alternating_of_family` /
  `alternatingBundleHom_of_family` plus an operator- or parameter-level input
  (`cpolynomialAt_alternatingMapAction_of_factorial_ne_zero`;
  `hasBoundedLift_of_finiteCoordinateDomain` + `cpolynomialAt_alternatingMapAction_of_boundedLift`;
  `isAdmissibleOn_of_c0`; `isAdmissibleOn_of_l1_retract`; `contDiff_alternatingMapAction`) and
  about 100 lines of glue in that file: a chart-level lemma copied from
  `contMDiffOn_alternatingMapAction_of_finiteCoordinates`, the c₀ retract step for families (not
  in the library), and a basis built from `X ≃L[K] (Fin d → K)`.
* `row1_spherical_bundle`, `row1_spherical_morphism`: not proved. The library's
  `cpolynomialAt_alternatingMapAction_of_sphericallyComplete` needs the given norm of the target
  fiber to be ultrametric and spherically complete (`[IsUltrametricDist F]
  [SphericallyCompleteSpace F]`); the transfer to a fiber that only *admits* an equivalent such
  norm is not formalized.
-/

open Bundle
open scoped Bundle Manifold ContDiff ZeroAtInfty

namespace AlternatingAnalyticChallenge.Cor4_6

universe uK uM uP uI uF₁ uF₂ uE₁ uE₂ uA uA' uB uB' uE uE' uF uF' uX

/-- `X` admits an equivalent nonarchimedean spherically complete norm: a seminorm `q` with the
strong triangle inequality and two-sided bounds against `‖·‖`, such that every nonempty family
of pairwise-intersecting closed `q`-balls has a common point. -/
def HasEquivalentSphericallyCompleteUltrametricNorm
    (K : Type uK) [NormedField K] (X : Type uX) [NormedAddCommGroup X] [NormedSpace K X] :
    Prop :=
  ∃ q : Seminorm K X,
    (∀ x y, q (x + y) ≤ max (q x) (q y)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ x, ‖x‖ ≤ C * q x) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ x, q x ≤ C * ‖x‖) ∧
    (∀ S : Set (X × ℝ), S.Nonempty →
      (∀ p ∈ S, ∀ p' ∈ S, ∃ z, q (z - p.1) ≤ p.2 ∧ q (z - p'.1) ≤ p'.2) →
      ∃ z, ∀ p ∈ S, q (z - p.1) ≤ p.2)

/-- **Corollary 4.6, Row 1, first alternative: arbitrary model `P`, `k! ≠ 0` in `K`.**
Object part (analytic alternating bundle). -/
theorem row1_factorial_bundle
    {K : Type uK} [NontriviallyNormedField K]
    {M : Type uM} [TopologicalSpace M]
    {P : Type uP} [NormedAddCommGroup P] [NormedSpace K P]
    [ChartedSpace P M] [IsManifold 𝓘(K, P) ω M]
    {F₁ : Type uF₁} [NormedAddCommGroup F₁] [NormedSpace K F₁]
    {F₂ : Type uF₂} [NormedAddCommGroup F₂] [NormedSpace K F₂]
    {E₁ : M → Type uE₁} {E₂ : M → Type uE₂}
    [∀ x, AddCommGroup (E₁ x)] [∀ x, Module K (E₁ x)]
    [∀ x, AddCommGroup (E₂ x)] [∀ x, Module K (E₂ x)]
    [∀ x, TopologicalSpace (E₁ x)] [∀ x, TopologicalSpace (E₂ x)]
    [∀ x, IsTopologicalAddGroup (E₁ x)] [∀ x, ContinuousSMul K (E₁ x)]
    [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul K (E₂ x)]
    [TopologicalSpace (TotalSpace F₁ E₁)] [TopologicalSpace (TotalSpace F₂ E₂)]
    [FiberBundle F₁ E₁] [VectorBundle K F₁ E₁]
    [FiberBundle F₂ E₂] [VectorBundle K F₂ E₂]
    [ContMDiffVectorBundle ω F₁ E₁ 𝓘(K, P)]
    [ContMDiffVectorBundle ω F₂ E₂ 𝓘(K, P)]
    (k : ℕ)
    (hk : (k.factorial : K) ≠ 0) :
    ContMDiffVectorBundle ω (F₁ [⋀^Fin k]→L[K] F₂)
      (fun x ↦ E₁ x [⋀^Fin k]→L[K] E₂ x) 𝓘(K, P) := by
  sorry

/-- **Corollary 4.6, Row 1, first alternative: arbitrary model `P`, `k! ≠ 0` in `K`.**
Morphism part (operator-valued morphisms). -/
theorem row1_factorial_morphism
    {K : Type uK} [NontriviallyNormedField K]
    {M : Type uM} [TopologicalSpace M]
    {P : Type uP} [NormedAddCommGroup P] [NormedSpace K P]
    [ChartedSpace P M] [IsManifold 𝓘(K, P) ω M]
    {A : Type uA} [NormedAddCommGroup A] [NormedSpace K A]
    {A' : Type uA'} [NormedAddCommGroup A'] [NormedSpace K A']
    {B : Type uB} [NormedAddCommGroup B] [NormedSpace K B]
    {B' : Type uB'} [NormedAddCommGroup B'] [NormedSpace K B']
    {E : M → Type uE} {E' : M → Type uE'} {F : M → Type uF} {F' : M → Type uF'}
    [∀ b, AddCommGroup (E b)] [∀ b, Module K (E b)] [∀ b, TopologicalSpace (E b)]
    [∀ b, AddCommGroup (E' b)] [∀ b, Module K (E' b)] [∀ b, TopologicalSpace (E' b)]
    [∀ b, AddCommGroup (F b)] [∀ b, Module K (F b)] [∀ b, TopologicalSpace (F b)]
    [∀ b, AddCommGroup (F' b)] [∀ b, Module K (F' b)] [∀ b, TopologicalSpace (F' b)]
    [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousSMul K (E b)]
    [∀ b, IsTopologicalAddGroup (E' b)] [∀ b, ContinuousSMul K (E' b)]
    [∀ b, IsTopologicalAddGroup (F b)] [∀ b, ContinuousSMul K (F b)]
    [∀ b, IsTopologicalAddGroup (F' b)] [∀ b, ContinuousSMul K (F' b)]
    [TopologicalSpace (TotalSpace A E)] [TopologicalSpace (TotalSpace A' E')]
    [TopologicalSpace (TotalSpace B F)] [TopologicalSpace (TotalSpace B' F')]
    [FiberBundle A E] [VectorBundle K A E]
    [FiberBundle A' E'] [VectorBundle K A' E']
    [FiberBundle B F] [VectorBundle K B F]
    [FiberBundle B' F'] [VectorBundle K B' F']
    [ContMDiffVectorBundle ω A E 𝓘(K, P)] [ContMDiffVectorBundle ω A' E' 𝓘(K, P)]
    [ContMDiffVectorBundle ω B F 𝓘(K, P)] [ContMDiffVectorBundle ω B' F' 𝓘(K, P)]
    (k : ℕ)
    (hk : (k.factorial : K) ≠ 0)
    (u : ContMDiffSection 𝓘(K, P) (A' →L[K] A) ω (fun b ↦ E' b →L[K] E b))
    (v : ContMDiffSection 𝓘(K, P) (B →L[K] B') ω (fun b ↦ F b →L[K] F' b)) :
    ∃ T : ContMDiffSection 𝓘(K, P)
        ((A [⋀^Fin k]→L[K] B) →L[K] (A' [⋀^Fin k]→L[K] B')) ω
        (fun b ↦ (E b [⋀^Fin k]→L[K] F b) →L[K] (E' b [⋀^Fin k]→L[K] F' b)),
      ∀ (b : M) (m : E b [⋀^Fin k]→L[K] F b),
        T b m = (v b).compContinuousAlternatingMap (m.compContinuousLinearMap (u b)) := by
  sorry

/-- **Corollary 4.6, Row 1, second alternative: arbitrary model `P`, `K` nonarchimedean and the target
fibers admit equivalent nonarchimedean spherically complete norms.**
Object part (analytic alternating bundle). -/
theorem row1_spherical_bundle
    {K : Type uK} [NontriviallyNormedField K]
    {M : Type uM} [TopologicalSpace M]
    {P : Type uP} [NormedAddCommGroup P] [NormedSpace K P]
    [ChartedSpace P M] [IsManifold 𝓘(K, P) ω M]
    [IsUltrametricDist K]
    {F₁ : Type uF₁} [NormedAddCommGroup F₁] [NormedSpace K F₁]
    {F₂ : Type uF₂} [NormedAddCommGroup F₂] [NormedSpace K F₂]
    {E₁ : M → Type uE₁} {E₂ : M → Type uE₂}
    [∀ x, AddCommGroup (E₁ x)] [∀ x, Module K (E₁ x)]
    [∀ x, AddCommGroup (E₂ x)] [∀ x, Module K (E₂ x)]
    [∀ x, TopologicalSpace (E₁ x)] [∀ x, TopologicalSpace (E₂ x)]
    [∀ x, IsTopologicalAddGroup (E₁ x)] [∀ x, ContinuousSMul K (E₁ x)]
    [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul K (E₂ x)]
    [TopologicalSpace (TotalSpace F₁ E₁)] [TopologicalSpace (TotalSpace F₂ E₂)]
    [FiberBundle F₁ E₁] [VectorBundle K F₁ E₁]
    [FiberBundle F₂ E₂] [VectorBundle K F₂ E₂]
    [ContMDiffVectorBundle ω F₁ E₁ 𝓘(K, P)]
    [ContMDiffVectorBundle ω F₂ E₂ 𝓘(K, P)]
    (k : ℕ)
    (hF₂ : HasEquivalentSphericallyCompleteUltrametricNorm K F₂) :
    ContMDiffVectorBundle ω (F₁ [⋀^Fin k]→L[K] F₂)
      (fun x ↦ E₁ x [⋀^Fin k]→L[K] E₂ x) 𝓘(K, P) := by
  sorry

/-- **Corollary 4.6, Row 1, second alternative: arbitrary model `P`, `K` nonarchimedean and the target
fibers admit equivalent nonarchimedean spherically complete norms.**
Morphism part (operator-valued morphisms). -/
theorem row1_spherical_morphism
    {K : Type uK} [NontriviallyNormedField K]
    {M : Type uM} [TopologicalSpace M]
    {P : Type uP} [NormedAddCommGroup P] [NormedSpace K P]
    [ChartedSpace P M] [IsManifold 𝓘(K, P) ω M]
    [IsUltrametricDist K]
    {A : Type uA} [NormedAddCommGroup A] [NormedSpace K A]
    {A' : Type uA'} [NormedAddCommGroup A'] [NormedSpace K A']
    {B : Type uB} [NormedAddCommGroup B] [NormedSpace K B]
    {B' : Type uB'} [NormedAddCommGroup B'] [NormedSpace K B']
    {E : M → Type uE} {E' : M → Type uE'} {F : M → Type uF} {F' : M → Type uF'}
    [∀ b, AddCommGroup (E b)] [∀ b, Module K (E b)] [∀ b, TopologicalSpace (E b)]
    [∀ b, AddCommGroup (E' b)] [∀ b, Module K (E' b)] [∀ b, TopologicalSpace (E' b)]
    [∀ b, AddCommGroup (F b)] [∀ b, Module K (F b)] [∀ b, TopologicalSpace (F b)]
    [∀ b, AddCommGroup (F' b)] [∀ b, Module K (F' b)] [∀ b, TopologicalSpace (F' b)]
    [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousSMul K (E b)]
    [∀ b, IsTopologicalAddGroup (E' b)] [∀ b, ContinuousSMul K (E' b)]
    [∀ b, IsTopologicalAddGroup (F b)] [∀ b, ContinuousSMul K (F b)]
    [∀ b, IsTopologicalAddGroup (F' b)] [∀ b, ContinuousSMul K (F' b)]
    [TopologicalSpace (TotalSpace A E)] [TopologicalSpace (TotalSpace A' E')]
    [TopologicalSpace (TotalSpace B F)] [TopologicalSpace (TotalSpace B' F')]
    [FiberBundle A E] [VectorBundle K A E]
    [FiberBundle A' E'] [VectorBundle K A' E']
    [FiberBundle B F] [VectorBundle K B F]
    [FiberBundle B' F'] [VectorBundle K B' F']
    [ContMDiffVectorBundle ω A E 𝓘(K, P)] [ContMDiffVectorBundle ω A' E' 𝓘(K, P)]
    [ContMDiffVectorBundle ω B F 𝓘(K, P)] [ContMDiffVectorBundle ω B' F' 𝓘(K, P)]
    (k : ℕ)
    (hB : HasEquivalentSphericallyCompleteUltrametricNorm K B)
    (hB' : HasEquivalentSphericallyCompleteUltrametricNorm K B')
    (u : ContMDiffSection 𝓘(K, P) (A' →L[K] A) ω (fun b ↦ E' b →L[K] E b))
    (v : ContMDiffSection 𝓘(K, P) (B →L[K] B') ω (fun b ↦ F b →L[K] F' b)) :
    ∃ T : ContMDiffSection 𝓘(K, P)
        ((A [⋀^Fin k]→L[K] B) →L[K] (A' [⋀^Fin k]→L[K] B')) ω
        (fun b ↦ (E b [⋀^Fin k]→L[K] F b) →L[K] (E' b [⋀^Fin k]→L[K] F' b)),
      ∀ (b : M) (m : E b [⋀^Fin k]→L[K] F b),
        T b m = (v b).compContinuousAlternatingMap (m.compContinuousLinearMap (u b)) := by
  sorry

/-- **Corollary 4.6, Row 1, third alternative: arbitrary model `P`, the source fibers have finite continuous
coordinates.**
Object part (analytic alternating bundle). -/
theorem row1_finiteSourceCoordinates_bundle
    {K : Type uK} [NontriviallyNormedField K]
    {M : Type uM} [TopologicalSpace M]
    {P : Type uP} [NormedAddCommGroup P] [NormedSpace K P]
    [ChartedSpace P M] [IsManifold 𝓘(K, P) ω M]
    {F₁ : Type uF₁} [NormedAddCommGroup F₁] [NormedSpace K F₁]
    {F₂ : Type uF₂} [NormedAddCommGroup F₂] [NormedSpace K F₂]
    {E₁ : M → Type uE₁} {E₂ : M → Type uE₂}
    [∀ x, AddCommGroup (E₁ x)] [∀ x, Module K (E₁ x)]
    [∀ x, AddCommGroup (E₂ x)] [∀ x, Module K (E₂ x)]
    [∀ x, TopologicalSpace (E₁ x)] [∀ x, TopologicalSpace (E₂ x)]
    [∀ x, IsTopologicalAddGroup (E₁ x)] [∀ x, ContinuousSMul K (E₁ x)]
    [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul K (E₂ x)]
    [TopologicalSpace (TotalSpace F₁ E₁)] [TopologicalSpace (TotalSpace F₂ E₂)]
    [FiberBundle F₁ E₁] [VectorBundle K F₁ E₁]
    [FiberBundle F₂ E₂] [VectorBundle K F₂ E₂]
    [ContMDiffVectorBundle ω F₁ E₁ 𝓘(K, P)]
    [ContMDiffVectorBundle ω F₂ E₂ 𝓘(K, P)]
    (k : ℕ)
    {d₁ : ℕ} (c₁ : F₁ ≃L[K] (Fin d₁ → K)) :
    ContMDiffVectorBundle ω (F₁ [⋀^Fin k]→L[K] F₂)
      (fun x ↦ E₁ x [⋀^Fin k]→L[K] E₂ x) 𝓘(K, P) := by
  sorry

/-- **Corollary 4.6, Row 1, third alternative: arbitrary model `P`, the source fibers have finite continuous
coordinates.**
Morphism part (operator-valued morphisms). -/
theorem row1_finiteSourceCoordinates_morphism
    {K : Type uK} [NontriviallyNormedField K]
    {M : Type uM} [TopologicalSpace M]
    {P : Type uP} [NormedAddCommGroup P] [NormedSpace K P]
    [ChartedSpace P M] [IsManifold 𝓘(K, P) ω M]
    {A : Type uA} [NormedAddCommGroup A] [NormedSpace K A]
    {A' : Type uA'} [NormedAddCommGroup A'] [NormedSpace K A']
    {B : Type uB} [NormedAddCommGroup B] [NormedSpace K B]
    {B' : Type uB'} [NormedAddCommGroup B'] [NormedSpace K B']
    {E : M → Type uE} {E' : M → Type uE'} {F : M → Type uF} {F' : M → Type uF'}
    [∀ b, AddCommGroup (E b)] [∀ b, Module K (E b)] [∀ b, TopologicalSpace (E b)]
    [∀ b, AddCommGroup (E' b)] [∀ b, Module K (E' b)] [∀ b, TopologicalSpace (E' b)]
    [∀ b, AddCommGroup (F b)] [∀ b, Module K (F b)] [∀ b, TopologicalSpace (F b)]
    [∀ b, AddCommGroup (F' b)] [∀ b, Module K (F' b)] [∀ b, TopologicalSpace (F' b)]
    [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousSMul K (E b)]
    [∀ b, IsTopologicalAddGroup (E' b)] [∀ b, ContinuousSMul K (E' b)]
    [∀ b, IsTopologicalAddGroup (F b)] [∀ b, ContinuousSMul K (F b)]
    [∀ b, IsTopologicalAddGroup (F' b)] [∀ b, ContinuousSMul K (F' b)]
    [TopologicalSpace (TotalSpace A E)] [TopologicalSpace (TotalSpace A' E')]
    [TopologicalSpace (TotalSpace B F)] [TopologicalSpace (TotalSpace B' F')]
    [FiberBundle A E] [VectorBundle K A E]
    [FiberBundle A' E'] [VectorBundle K A' E']
    [FiberBundle B F] [VectorBundle K B F]
    [FiberBundle B' F'] [VectorBundle K B' F']
    [ContMDiffVectorBundle ω A E 𝓘(K, P)] [ContMDiffVectorBundle ω A' E' 𝓘(K, P)]
    [ContMDiffVectorBundle ω B F 𝓘(K, P)] [ContMDiffVectorBundle ω B' F' 𝓘(K, P)]
    (k : ℕ)
    {dA : ℕ} (cA : A ≃L[K] (Fin dA → K)) {dA' : ℕ} (cA' : A' ≃L[K] (Fin dA' → K))
    (u : ContMDiffSection 𝓘(K, P) (A' →L[K] A) ω (fun b ↦ E' b →L[K] E b))
    (v : ContMDiffSection 𝓘(K, P) (B →L[K] B') ω (fun b ↦ F b →L[K] F' b)) :
    ∃ T : ContMDiffSection 𝓘(K, P)
        ((A [⋀^Fin k]→L[K] B) →L[K] (A' [⋀^Fin k]→L[K] B')) ω
        (fun b ↦ (E b [⋀^Fin k]→L[K] F b) →L[K] (E' b [⋀^Fin k]→L[K] F' b)),
      ∀ (b : M) (m : E b [⋀^Fin k]→L[K] F b),
        T b m = (v b).compContinuousAlternatingMap (m.compContinuousLinearMap (u b)) := by
  sorry

/-- **Corollary 4.6, Row 2: the base model `P` has finite continuous coordinates; arbitrary normed fibers.**
Object part (analytic alternating bundle). -/
theorem row2_finiteCoordinateBase_bundle
    {K : Type uK} [NontriviallyNormedField K]
    {M : Type uM} [TopologicalSpace M]
    {P : Type uP} [NormedAddCommGroup P] [NormedSpace K P]
    [ChartedSpace P M] [IsManifold 𝓘(K, P) ω M]
    {d : ℕ} (c : P ≃L[K] (Fin d → K))
    {F₁ : Type uF₁} [NormedAddCommGroup F₁] [NormedSpace K F₁]
    {F₂ : Type uF₂} [NormedAddCommGroup F₂] [NormedSpace K F₂]
    {E₁ : M → Type uE₁} {E₂ : M → Type uE₂}
    [∀ x, AddCommGroup (E₁ x)] [∀ x, Module K (E₁ x)]
    [∀ x, AddCommGroup (E₂ x)] [∀ x, Module K (E₂ x)]
    [∀ x, TopologicalSpace (E₁ x)] [∀ x, TopologicalSpace (E₂ x)]
    [∀ x, IsTopologicalAddGroup (E₁ x)] [∀ x, ContinuousSMul K (E₁ x)]
    [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul K (E₂ x)]
    [TopologicalSpace (TotalSpace F₁ E₁)] [TopologicalSpace (TotalSpace F₂ E₂)]
    [FiberBundle F₁ E₁] [VectorBundle K F₁ E₁]
    [FiberBundle F₂ E₂] [VectorBundle K F₂ E₂]
    [ContMDiffVectorBundle ω F₁ E₁ 𝓘(K, P)]
    [ContMDiffVectorBundle ω F₂ E₂ 𝓘(K, P)]
    (k : ℕ) :
    ContMDiffVectorBundle ω (F₁ [⋀^Fin k]→L[K] F₂)
      (fun x ↦ E₁ x [⋀^Fin k]→L[K] E₂ x) 𝓘(K, P) := by
  sorry

/-- **Corollary 4.6, Row 2: the base model `P` has finite continuous coordinates; arbitrary normed fibers.**
Morphism part (operator-valued morphisms). -/
theorem row2_finiteCoordinateBase_morphism
    {K : Type uK} [NontriviallyNormedField K]
    {M : Type uM} [TopologicalSpace M]
    {P : Type uP} [NormedAddCommGroup P] [NormedSpace K P]
    [ChartedSpace P M] [IsManifold 𝓘(K, P) ω M]
    {d : ℕ} (c : P ≃L[K] (Fin d → K))
    {A : Type uA} [NormedAddCommGroup A] [NormedSpace K A]
    {A' : Type uA'} [NormedAddCommGroup A'] [NormedSpace K A']
    {B : Type uB} [NormedAddCommGroup B] [NormedSpace K B]
    {B' : Type uB'} [NormedAddCommGroup B'] [NormedSpace K B']
    {E : M → Type uE} {E' : M → Type uE'} {F : M → Type uF} {F' : M → Type uF'}
    [∀ b, AddCommGroup (E b)] [∀ b, Module K (E b)] [∀ b, TopologicalSpace (E b)]
    [∀ b, AddCommGroup (E' b)] [∀ b, Module K (E' b)] [∀ b, TopologicalSpace (E' b)]
    [∀ b, AddCommGroup (F b)] [∀ b, Module K (F b)] [∀ b, TopologicalSpace (F b)]
    [∀ b, AddCommGroup (F' b)] [∀ b, Module K (F' b)] [∀ b, TopologicalSpace (F' b)]
    [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousSMul K (E b)]
    [∀ b, IsTopologicalAddGroup (E' b)] [∀ b, ContinuousSMul K (E' b)]
    [∀ b, IsTopologicalAddGroup (F b)] [∀ b, ContinuousSMul K (F b)]
    [∀ b, IsTopologicalAddGroup (F' b)] [∀ b, ContinuousSMul K (F' b)]
    [TopologicalSpace (TotalSpace A E)] [TopologicalSpace (TotalSpace A' E')]
    [TopologicalSpace (TotalSpace B F)] [TopologicalSpace (TotalSpace B' F')]
    [FiberBundle A E] [VectorBundle K A E]
    [FiberBundle A' E'] [VectorBundle K A' E']
    [FiberBundle B F] [VectorBundle K B F]
    [FiberBundle B' F'] [VectorBundle K B' F']
    [ContMDiffVectorBundle ω A E 𝓘(K, P)] [ContMDiffVectorBundle ω A' E' 𝓘(K, P)]
    [ContMDiffVectorBundle ω B F 𝓘(K, P)] [ContMDiffVectorBundle ω B' F' 𝓘(K, P)]
    (k : ℕ)
    (u : ContMDiffSection 𝓘(K, P) (A' →L[K] A) ω (fun b ↦ E' b →L[K] E b))
    (v : ContMDiffSection 𝓘(K, P) (B →L[K] B') ω (fun b ↦ F b →L[K] F' b)) :
    ∃ T : ContMDiffSection 𝓘(K, P)
        ((A [⋀^Fin k]→L[K] B) →L[K] (A' [⋀^Fin k]→L[K] B')) ω
        (fun b ↦ (E b [⋀^Fin k]→L[K] F b) →L[K] (E' b [⋀^Fin k]→L[K] F' b)),
      ∀ (b : M) (m : E b [⋀^Fin k]→L[K] F b),
        T b m = (v b).compContinuousAlternatingMap (m.compContinuousLinearMap (u b)) := by
  sorry

/-- **Corollary 4.6, Row 3: the base model `P` is `c₀(I, K)` or a bounded linear retract of it; `K`
nonarchimedean; complete nonarchimedean target fibers.**
Object part (analytic alternating bundle). -/
theorem row3_c0Retract_bundle
    {K : Type uK} [NontriviallyNormedField K]
    {M : Type uM} [TopologicalSpace M]
    {P : Type uP} [NormedAddCommGroup P] [NormedSpace K P]
    [ChartedSpace P M] [IsManifold 𝓘(K, P) ω M]
    [IsUltrametricDist K]
    {I : Type uI} [TopologicalSpace I] [DiscreteTopology I]
    (i : P →L[K] C₀(I, K)) (r : C₀(I, K) →L[K] P)
    (hri : r.comp i = ContinuousLinearMap.id K P)
    {F₁ : Type uF₁} [NormedAddCommGroup F₁] [NormedSpace K F₁]
    {F₂ : Type uF₂} [NormedAddCommGroup F₂] [NormedSpace K F₂]
    {E₁ : M → Type uE₁} {E₂ : M → Type uE₂}
    [∀ x, AddCommGroup (E₁ x)] [∀ x, Module K (E₁ x)]
    [∀ x, AddCommGroup (E₂ x)] [∀ x, Module K (E₂ x)]
    [∀ x, TopologicalSpace (E₁ x)] [∀ x, TopologicalSpace (E₂ x)]
    [∀ x, IsTopologicalAddGroup (E₁ x)] [∀ x, ContinuousSMul K (E₁ x)]
    [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul K (E₂ x)]
    [TopologicalSpace (TotalSpace F₁ E₁)] [TopologicalSpace (TotalSpace F₂ E₂)]
    [FiberBundle F₁ E₁] [VectorBundle K F₁ E₁]
    [FiberBundle F₂ E₂] [VectorBundle K F₂ E₂]
    [ContMDiffVectorBundle ω F₁ E₁ 𝓘(K, P)]
    [ContMDiffVectorBundle ω F₂ E₂ 𝓘(K, P)]
    (k : ℕ)
    [CompleteSpace F₂] [IsUltrametricDist F₂] :
    ContMDiffVectorBundle ω (F₁ [⋀^Fin k]→L[K] F₂)
      (fun x ↦ E₁ x [⋀^Fin k]→L[K] E₂ x) 𝓘(K, P) := by
  sorry

/-- **Corollary 4.6, Row 3: the base model `P` is `c₀(I, K)` or a bounded linear retract of it; `K`
nonarchimedean; complete nonarchimedean target fibers.**
Morphism part (operator-valued morphisms). -/
theorem row3_c0Retract_morphism
    {K : Type uK} [NontriviallyNormedField K]
    {M : Type uM} [TopologicalSpace M]
    {P : Type uP} [NormedAddCommGroup P] [NormedSpace K P]
    [ChartedSpace P M] [IsManifold 𝓘(K, P) ω M]
    [IsUltrametricDist K]
    {I : Type uI} [TopologicalSpace I] [DiscreteTopology I]
    (i : P →L[K] C₀(I, K)) (r : C₀(I, K) →L[K] P)
    (hri : r.comp i = ContinuousLinearMap.id K P)
    {A : Type uA} [NormedAddCommGroup A] [NormedSpace K A]
    {A' : Type uA'} [NormedAddCommGroup A'] [NormedSpace K A']
    {B : Type uB} [NormedAddCommGroup B] [NormedSpace K B]
    {B' : Type uB'} [NormedAddCommGroup B'] [NormedSpace K B']
    {E : M → Type uE} {E' : M → Type uE'} {F : M → Type uF} {F' : M → Type uF'}
    [∀ b, AddCommGroup (E b)] [∀ b, Module K (E b)] [∀ b, TopologicalSpace (E b)]
    [∀ b, AddCommGroup (E' b)] [∀ b, Module K (E' b)] [∀ b, TopologicalSpace (E' b)]
    [∀ b, AddCommGroup (F b)] [∀ b, Module K (F b)] [∀ b, TopologicalSpace (F b)]
    [∀ b, AddCommGroup (F' b)] [∀ b, Module K (F' b)] [∀ b, TopologicalSpace (F' b)]
    [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousSMul K (E b)]
    [∀ b, IsTopologicalAddGroup (E' b)] [∀ b, ContinuousSMul K (E' b)]
    [∀ b, IsTopologicalAddGroup (F b)] [∀ b, ContinuousSMul K (F b)]
    [∀ b, IsTopologicalAddGroup (F' b)] [∀ b, ContinuousSMul K (F' b)]
    [TopologicalSpace (TotalSpace A E)] [TopologicalSpace (TotalSpace A' E')]
    [TopologicalSpace (TotalSpace B F)] [TopologicalSpace (TotalSpace B' F')]
    [FiberBundle A E] [VectorBundle K A E]
    [FiberBundle A' E'] [VectorBundle K A' E']
    [FiberBundle B F] [VectorBundle K B F]
    [FiberBundle B' F'] [VectorBundle K B' F']
    [ContMDiffVectorBundle ω A E 𝓘(K, P)] [ContMDiffVectorBundle ω A' E' 𝓘(K, P)]
    [ContMDiffVectorBundle ω B F 𝓘(K, P)] [ContMDiffVectorBundle ω B' F' 𝓘(K, P)]
    (k : ℕ)
    [CompleteSpace B] [IsUltrametricDist B] [CompleteSpace B'] [IsUltrametricDist B']
    (u : ContMDiffSection 𝓘(K, P) (A' →L[K] A) ω (fun b ↦ E' b →L[K] E b))
    (v : ContMDiffSection 𝓘(K, P) (B →L[K] B') ω (fun b ↦ F b →L[K] F' b)) :
    ∃ T : ContMDiffSection 𝓘(K, P)
        ((A [⋀^Fin k]→L[K] B) →L[K] (A' [⋀^Fin k]→L[K] B')) ω
        (fun b ↦ (E b [⋀^Fin k]→L[K] F b) →L[K] (E' b [⋀^Fin k]→L[K] F' b)),
      ∀ (b : M) (m : E b [⋀^Fin k]→L[K] F b),
        T b m = (v b).compContinuousAlternatingMap (m.compContinuousLinearMap (u b)) := by
  sorry

/-- **Corollary 4.6, Row 4: the base model `P` is `ℓ¹(I, K)` or a bounded linear retract of it; complete
target fibers.**
Object part (analytic alternating bundle). -/
theorem row4_l1Retract_bundle
    {K : Type uK} [NontriviallyNormedField K]
    {M : Type uM} [TopologicalSpace M]
    {P : Type uP} [NormedAddCommGroup P] [NormedSpace K P]
    [ChartedSpace P M] [IsManifold 𝓘(K, P) ω M]
    {I : Type uI}
    (i : P →L[K] lp (fun _ : I => K) 1) (r : lp (fun _ : I => K) 1 →L[K] P)
    (hri : r.comp i = ContinuousLinearMap.id K P)
    {F₁ : Type uF₁} [NormedAddCommGroup F₁] [NormedSpace K F₁]
    {F₂ : Type uF₂} [NormedAddCommGroup F₂] [NormedSpace K F₂]
    {E₁ : M → Type uE₁} {E₂ : M → Type uE₂}
    [∀ x, AddCommGroup (E₁ x)] [∀ x, Module K (E₁ x)]
    [∀ x, AddCommGroup (E₂ x)] [∀ x, Module K (E₂ x)]
    [∀ x, TopologicalSpace (E₁ x)] [∀ x, TopologicalSpace (E₂ x)]
    [∀ x, IsTopologicalAddGroup (E₁ x)] [∀ x, ContinuousSMul K (E₁ x)]
    [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul K (E₂ x)]
    [TopologicalSpace (TotalSpace F₁ E₁)] [TopologicalSpace (TotalSpace F₂ E₂)]
    [FiberBundle F₁ E₁] [VectorBundle K F₁ E₁]
    [FiberBundle F₂ E₂] [VectorBundle K F₂ E₂]
    [ContMDiffVectorBundle ω F₁ E₁ 𝓘(K, P)]
    [ContMDiffVectorBundle ω F₂ E₂ 𝓘(K, P)]
    (k : ℕ)
    [CompleteSpace F₂] :
    ContMDiffVectorBundle ω (F₁ [⋀^Fin k]→L[K] F₂)
      (fun x ↦ E₁ x [⋀^Fin k]→L[K] E₂ x) 𝓘(K, P) := by
  sorry

/-- **Corollary 4.6, Row 4: the base model `P` is `ℓ¹(I, K)` or a bounded linear retract of it; complete
target fibers.**
Morphism part (operator-valued morphisms). -/
theorem row4_l1Retract_morphism
    {K : Type uK} [NontriviallyNormedField K]
    {M : Type uM} [TopologicalSpace M]
    {P : Type uP} [NormedAddCommGroup P] [NormedSpace K P]
    [ChartedSpace P M] [IsManifold 𝓘(K, P) ω M]
    {I : Type uI}
    (i : P →L[K] lp (fun _ : I => K) 1) (r : lp (fun _ : I => K) 1 →L[K] P)
    (hri : r.comp i = ContinuousLinearMap.id K P)
    {A : Type uA} [NormedAddCommGroup A] [NormedSpace K A]
    {A' : Type uA'} [NormedAddCommGroup A'] [NormedSpace K A']
    {B : Type uB} [NormedAddCommGroup B] [NormedSpace K B]
    {B' : Type uB'} [NormedAddCommGroup B'] [NormedSpace K B']
    {E : M → Type uE} {E' : M → Type uE'} {F : M → Type uF} {F' : M → Type uF'}
    [∀ b, AddCommGroup (E b)] [∀ b, Module K (E b)] [∀ b, TopologicalSpace (E b)]
    [∀ b, AddCommGroup (E' b)] [∀ b, Module K (E' b)] [∀ b, TopologicalSpace (E' b)]
    [∀ b, AddCommGroup (F b)] [∀ b, Module K (F b)] [∀ b, TopologicalSpace (F b)]
    [∀ b, AddCommGroup (F' b)] [∀ b, Module K (F' b)] [∀ b, TopologicalSpace (F' b)]
    [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousSMul K (E b)]
    [∀ b, IsTopologicalAddGroup (E' b)] [∀ b, ContinuousSMul K (E' b)]
    [∀ b, IsTopologicalAddGroup (F b)] [∀ b, ContinuousSMul K (F b)]
    [∀ b, IsTopologicalAddGroup (F' b)] [∀ b, ContinuousSMul K (F' b)]
    [TopologicalSpace (TotalSpace A E)] [TopologicalSpace (TotalSpace A' E')]
    [TopologicalSpace (TotalSpace B F)] [TopologicalSpace (TotalSpace B' F')]
    [FiberBundle A E] [VectorBundle K A E]
    [FiberBundle A' E'] [VectorBundle K A' E']
    [FiberBundle B F] [VectorBundle K B F]
    [FiberBundle B' F'] [VectorBundle K B' F']
    [ContMDiffVectorBundle ω A E 𝓘(K, P)] [ContMDiffVectorBundle ω A' E' 𝓘(K, P)]
    [ContMDiffVectorBundle ω B F 𝓘(K, P)] [ContMDiffVectorBundle ω B' F' 𝓘(K, P)]
    (k : ℕ)
    [CompleteSpace B] [CompleteSpace B']
    (u : ContMDiffSection 𝓘(K, P) (A' →L[K] A) ω (fun b ↦ E' b →L[K] E b))
    (v : ContMDiffSection 𝓘(K, P) (B →L[K] B') ω (fun b ↦ F b →L[K] F' b)) :
    ∃ T : ContMDiffSection 𝓘(K, P)
        ((A [⋀^Fin k]→L[K] B) →L[K] (A' [⋀^Fin k]→L[K] B')) ω
        (fun b ↦ (E b [⋀^Fin k]→L[K] F b) →L[K] (E' b [⋀^Fin k]→L[K] F' b)),
      ∀ (b : M) (m : E b [⋀^Fin k]→L[K] F b),
        T b m = (v b).compContinuousAlternatingMap (m.compContinuousLinearMap (u b)) := by
  sorry

/-- **Corollary 4.6, Final sentence: at every finite smoothness order and at `C^∞` (`n : ℕ∞`), no hypothesis
on `K`, `P` or the fibers.**
Object part (analytic alternating bundle). -/
theorem smooth_bundle
    {K : Type uK} [NontriviallyNormedField K]
    {M : Type uM} [TopologicalSpace M]
    (n : ℕ∞)
    {P : Type uP} [NormedAddCommGroup P] [NormedSpace K P]
    [ChartedSpace P M] [IsManifold 𝓘(K, P) (n : WithTop ℕ∞) M]
    {F₁ : Type uF₁} [NormedAddCommGroup F₁] [NormedSpace K F₁]
    {F₂ : Type uF₂} [NormedAddCommGroup F₂] [NormedSpace K F₂]
    {E₁ : M → Type uE₁} {E₂ : M → Type uE₂}
    [∀ x, AddCommGroup (E₁ x)] [∀ x, Module K (E₁ x)]
    [∀ x, AddCommGroup (E₂ x)] [∀ x, Module K (E₂ x)]
    [∀ x, TopologicalSpace (E₁ x)] [∀ x, TopologicalSpace (E₂ x)]
    [∀ x, IsTopologicalAddGroup (E₁ x)] [∀ x, ContinuousSMul K (E₁ x)]
    [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul K (E₂ x)]
    [TopologicalSpace (TotalSpace F₁ E₁)] [TopologicalSpace (TotalSpace F₂ E₂)]
    [FiberBundle F₁ E₁] [VectorBundle K F₁ E₁]
    [FiberBundle F₂ E₂] [VectorBundle K F₂ E₂]
    [ContMDiffVectorBundle (n : WithTop ℕ∞) F₁ E₁ 𝓘(K, P)]
    [ContMDiffVectorBundle (n : WithTop ℕ∞) F₂ E₂ 𝓘(K, P)]
    (k : ℕ) :
    ContMDiffVectorBundle (n : WithTop ℕ∞) (F₁ [⋀^Fin k]→L[K] F₂)
      (fun x ↦ E₁ x [⋀^Fin k]→L[K] E₂ x) 𝓘(K, P) := by
  sorry

/-- **Corollary 4.6, Final sentence: at every finite smoothness order and at `C^∞` (`n : ℕ∞`), no hypothesis
on `K`, `P` or the fibers.**
Morphism part (operator-valued morphisms). -/
theorem smooth_morphism
    {K : Type uK} [NontriviallyNormedField K]
    {M : Type uM} [TopologicalSpace M]
    (n : ℕ∞)
    {P : Type uP} [NormedAddCommGroup P] [NormedSpace K P]
    [ChartedSpace P M] [IsManifold 𝓘(K, P) (n : WithTop ℕ∞) M]
    {A : Type uA} [NormedAddCommGroup A] [NormedSpace K A]
    {A' : Type uA'} [NormedAddCommGroup A'] [NormedSpace K A']
    {B : Type uB} [NormedAddCommGroup B] [NormedSpace K B]
    {B' : Type uB'} [NormedAddCommGroup B'] [NormedSpace K B']
    {E : M → Type uE} {E' : M → Type uE'} {F : M → Type uF} {F' : M → Type uF'}
    [∀ b, AddCommGroup (E b)] [∀ b, Module K (E b)] [∀ b, TopologicalSpace (E b)]
    [∀ b, AddCommGroup (E' b)] [∀ b, Module K (E' b)] [∀ b, TopologicalSpace (E' b)]
    [∀ b, AddCommGroup (F b)] [∀ b, Module K (F b)] [∀ b, TopologicalSpace (F b)]
    [∀ b, AddCommGroup (F' b)] [∀ b, Module K (F' b)] [∀ b, TopologicalSpace (F' b)]
    [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousSMul K (E b)]
    [∀ b, IsTopologicalAddGroup (E' b)] [∀ b, ContinuousSMul K (E' b)]
    [∀ b, IsTopologicalAddGroup (F b)] [∀ b, ContinuousSMul K (F b)]
    [∀ b, IsTopologicalAddGroup (F' b)] [∀ b, ContinuousSMul K (F' b)]
    [TopologicalSpace (TotalSpace A E)] [TopologicalSpace (TotalSpace A' E')]
    [TopologicalSpace (TotalSpace B F)] [TopologicalSpace (TotalSpace B' F')]
    [FiberBundle A E] [VectorBundle K A E]
    [FiberBundle A' E'] [VectorBundle K A' E']
    [FiberBundle B F] [VectorBundle K B F]
    [FiberBundle B' F'] [VectorBundle K B' F']
    [ContMDiffVectorBundle (n : WithTop ℕ∞) A E 𝓘(K, P)] [ContMDiffVectorBundle (n : WithTop ℕ∞) A' E' 𝓘(K, P)]
    [ContMDiffVectorBundle (n : WithTop ℕ∞) B F 𝓘(K, P)] [ContMDiffVectorBundle (n : WithTop ℕ∞) B' F' 𝓘(K, P)]
    (k : ℕ)
    (u : ContMDiffSection 𝓘(K, P) (A' →L[K] A) (n : WithTop ℕ∞) (fun b ↦ E' b →L[K] E b))
    (v : ContMDiffSection 𝓘(K, P) (B →L[K] B') (n : WithTop ℕ∞) (fun b ↦ F b →L[K] F' b)) :
    ∃ T : ContMDiffSection 𝓘(K, P)
        ((A [⋀^Fin k]→L[K] B) →L[K] (A' [⋀^Fin k]→L[K] B')) (n : WithTop ℕ∞)
        (fun b ↦ (E b [⋀^Fin k]→L[K] F b) →L[K] (E' b [⋀^Fin k]→L[K] F' b)),
      ∀ (b : M) (m : E b [⋀^Fin k]→L[K] F b),
        T b m = (v b).compContinuousAlternatingMap (m.compContinuousLinearMap (u b)) := by
  sorry
end AlternatingAnalyticChallenge.Cor4_6
