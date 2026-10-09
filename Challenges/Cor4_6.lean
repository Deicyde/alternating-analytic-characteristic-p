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

Paper statement (Section 4.3): Let `M` be an analytic manifold over `K`, with
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
* Two theorems per setting, `<setting>_bundle` (objects) and `<setting>_morphism` (morphisms):
  the three alternatives of row 1, rows 2-4, and the `C^n`/`C^∞` sentence. The functor laws
  follow pointwise from the fiber formula and are not stated.
* Analytic manifold: `[ChartedSpace P M] [IsManifold 𝓘(K, P) ω M]`, so no boundary or corners.
  Analytic vector bundle: `FiberBundle`, `VectorBundle` and `ContMDiffVectorBundle ω _ _ 𝓘(K, P)`
  with normed model fiber.
* Objects: the bundle `x ↦ E₁ x [⋀^Fin k]→L[K] E₂ x` with Mathlib's topology and trivializations
  is `ContMDiffVectorBundle ω` with model fiber `F₁ [⋀^Fin k]→L[K] F₂`.
* Morphisms: `u`, `v` are analytic sections of Hom bundles (`u` contravariant, `v` covariant);
  the conclusion is that `m ↦ v ∘ m ∘ (u, …, u)` is an analytic section of the Hom bundle
  between the alternating bundles. Source typical fibers are `A, A'`, target `B, B'`.
* "Finite continuous coordinates" for `X` is `X ≃L[K] (Fin d → K)`; `k! ≠ 0` is
  `((k.factorial : ℕ) : K) ≠ 0`; "nonarchimedean" is `IsUltrametricDist`.
* "Admits an equivalent nonarchimedean spherically complete norm" is the definition
  `HasEquivalentSphericallyCompleteUltrametricNorm` below, stated for seminorm balls.
* `c₀(I, K)` is `C₀(I, K)` for discrete `I`; `ℓ¹(I, K)` is `lp (fun _ : I => K) 1`. "A bounded
  linear retract" is `i : P → V`, `r : V → P`, `r ∘ i = id`, which includes `P = V`.
* The `C^n`/`C^∞` sentence takes `n : ℕ∞`, a `C^n` manifold, `C^n` bundles and sections.
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

/-- Corollary 4.6, row 1, `k! ≠ 0` in `K`: the alternating bundle is analytic. -/
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

/-- Corollary 4.6, row 1, `k! ≠ 0` in `K`: analytic morphisms induce an analytic morphism. -/
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

/-- Corollary 4.6, row 1, `K` nonarchimedean and target fibers with an equivalent
spherically complete ultrametric norm: the alternating bundle is analytic. -/
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

/-- Corollary 4.6, row 1, `K` nonarchimedean and target fibers with an equivalent
spherically complete ultrametric norm: analytic morphisms induce an analytic morphism. -/
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

/-- Corollary 4.6, row 1, source fibers with finite continuous coordinates: the alternating
bundle is analytic. -/
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

/-- Corollary 4.6, row 1, source fibers with finite continuous coordinates: analytic
morphisms induce an analytic morphism. -/
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

/-- Corollary 4.6, row 2, model `P` with finite continuous coordinates: the alternating
bundle is analytic. -/
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

/-- Corollary 4.6, row 2, model `P` with finite continuous coordinates: analytic morphisms
induce an analytic morphism. -/
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

/-- Corollary 4.6, row 3, model a retract of `c₀(I, K)`, `K` nonarchimedean, complete
nonarchimedean target fibers: the alternating bundle is analytic. -/
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

/-- Corollary 4.6, row 3, model a retract of `c₀(I, K)`, `K` nonarchimedean, complete
nonarchimedean target fibers: analytic morphisms induce an analytic morphism. -/
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

/-- Corollary 4.6, row 4, model a retract of `ℓ¹(I, K)`, complete target fibers: the
alternating bundle is analytic. -/
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

/-- Corollary 4.6, row 4, model a retract of `ℓ¹(I, K)`, complete target fibers: analytic
morphisms induce an analytic morphism. -/
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

/-- Corollary 4.6, last sentence: for `n : ℕ∞`, the alternating bundle of `C^n` bundles
is `C^n`. -/
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

/-- Corollary 4.6, last sentence: for `n : ℕ∞`, `C^n` morphisms induce a `C^n` morphism. -/
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
