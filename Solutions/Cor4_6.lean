import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Topology.VectorBundle.ContinuousAlternatingMap
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Module.Seminorm.Basic
import AlternatingAnalytic.Geometry.BundleRows.ActionFamilies

/-!
# Corollary 4.6 (the bundle theorem), p. 12

Solution: the 14 statements of `Challenges/Cor4_6.lean`, proved from the library. Each object
part is `AlternatingAnalytic.contMDiffVectorBundle_alternating_of_family` and each morphism part
is `AlternatingAnalytic.alternatingBundleHom_of_family` (`Geometry/AnalyticAlternatingBundle.lean`,
`Geometry/AnalyticAlternatingBundleMorphism.lean`), fed with the family-preservation input of its
setting from `Geometry/BundleRows/ActionFamilies.lean`:
* row 1, `k! ≠ 0`: `BundleRows.hloc_factorial`;
* row 1, equivalent spherically complete ultrametric target norm:
  `BundleRows.hloc_equivalentSphericalNorm`, from the transfer
  `EquivalentSphericalNorm.hasBoundedLift_of_equivalentSphericalNorm`
  (`Geometry/BundleRows/EquivalentSphericalNorm.lean`);
* row 1, finite-coordinate source: `BundleRows.hloc_finiteSource`;
* row 2: `contMDiffVectorBundle_alternating_of_finiteCoordinates`,
  `alternatingBundleHom_of_finiteCoordinates`;
* row 3: `BundleRows.hloc_c0_retract`; row 4: `isAdmissibleOn_of_l1_retract`;
* `C^n`, `C^∞`: `BundleRows.smooth_family`.
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
  exact AlternatingAnalytic.contMDiffVectorBundle_alternating_of_family k
    (fun {_} hU {_} hγ ↦ AlternatingAnalytic.BundleRows.glue_contMDiffOn_alternatingMapAction k
      (fun {_} {_} hV hγ' ↦ AlternatingAnalytic.BundleRows.hloc_factorial k hk hV hγ') hU hγ)

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
  letI := AlternatingAnalytic.contMDiffVectorBundle_alternating_of_family (I := 𝓘(K, P)) (F₁ := A) (E₁ := E) (F₂ := B) (E₂ := F) k
    (fun {_} hU {_} hγ ↦ AlternatingAnalytic.BundleRows.glue_contMDiffOn_alternatingMapAction k
      (fun {_} {_} hV hγ' ↦ AlternatingAnalytic.BundleRows.hloc_factorial k hk hV hγ') hU hγ)
  letI := AlternatingAnalytic.contMDiffVectorBundle_alternating_of_family (I := 𝓘(K, P)) (F₁ := A') (E₁ := E') (F₂ := B') (E₂ := F') k
    (fun {_} hU {_} hγ ↦ AlternatingAnalytic.BundleRows.glue_contMDiffOn_alternatingMapAction k
      (fun {_} {_} hV hγ' ↦ AlternatingAnalytic.BundleRows.hloc_factorial k hk hV hγ') hU hγ)
  exact ⟨AlternatingAnalytic.alternatingBundleHom_of_family (I := 𝓘(K, P)) k
    (fun {_} hU {_} hγ ↦ AlternatingAnalytic.BundleRows.glue_contMDiffOn_alternatingMapAction k
      (fun {_} {_} hV hγ' ↦ AlternatingAnalytic.BundleRows.hloc_factorial k hk hV hγ') hU hγ) u v, fun _ _ ↦ rfl⟩

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
  exact AlternatingAnalytic.contMDiffVectorBundle_alternating_of_family k
    (fun {_} hU {_} hγ ↦ AlternatingAnalytic.BundleRows.glue_contMDiffOn_alternatingMapAction k
      (fun {_} {_} hV hγ' ↦
        AlternatingAnalytic.BundleRows.hloc_equivalentSphericalNorm k hF₂ hV hγ') hU hγ)

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
  letI := AlternatingAnalytic.contMDiffVectorBundle_alternating_of_family (I := 𝓘(K, P)) (F₁ := A) (E₁ := E) (F₂ := B) (E₂ := F) k
    (fun {_} hU {_} hγ ↦ AlternatingAnalytic.BundleRows.glue_contMDiffOn_alternatingMapAction k
      (fun {_} {_} hV hγ' ↦
        AlternatingAnalytic.BundleRows.hloc_equivalentSphericalNorm k hB hV hγ') hU hγ)
  letI := AlternatingAnalytic.contMDiffVectorBundle_alternating_of_family (I := 𝓘(K, P)) (F₁ := A') (E₁ := E') (F₂ := B') (E₂ := F') k
    (fun {_} hU {_} hγ ↦ AlternatingAnalytic.BundleRows.glue_contMDiffOn_alternatingMapAction k
      (fun {_} {_} hV hγ' ↦
        AlternatingAnalytic.BundleRows.hloc_equivalentSphericalNorm k hB' hV hγ') hU hγ)
  exact ⟨AlternatingAnalytic.alternatingBundleHom_of_family (I := 𝓘(K, P)) k
    (fun {_} hU {_} hγ ↦ AlternatingAnalytic.BundleRows.glue_contMDiffOn_alternatingMapAction k
      (fun {_} {_} hV hγ' ↦
        AlternatingAnalytic.BundleRows.hloc_equivalentSphericalNorm k hB hV hγ') hU hγ) u v,
    fun _ _ ↦ rfl⟩

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
  exact AlternatingAnalytic.contMDiffVectorBundle_alternating_of_family k
    (fun {_} hU {_} hγ ↦ AlternatingAnalytic.BundleRows.glue_contMDiffOn_alternatingMapAction k
      (fun {_} {_} hV hγ' ↦ AlternatingAnalytic.BundleRows.hloc_finiteSource k c₁ hV hγ') hU hγ)

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
  letI := AlternatingAnalytic.contMDiffVectorBundle_alternating_of_family (I := 𝓘(K, P)) (F₁ := A) (E₁ := E) (F₂ := B) (E₂ := F) k
    (fun {_} hU {_} hγ ↦ AlternatingAnalytic.BundleRows.glue_contMDiffOn_alternatingMapAction k
      (fun {_} {_} hV hγ' ↦ AlternatingAnalytic.BundleRows.hloc_finiteSource k cA hV hγ') hU hγ)
  letI := AlternatingAnalytic.contMDiffVectorBundle_alternating_of_family (I := 𝓘(K, P)) (F₁ := A') (E₁ := E') (F₂ := B') (E₂ := F') k
    (fun {_} hU {_} hγ ↦ AlternatingAnalytic.BundleRows.glue_contMDiffOn_alternatingMapAction k
      (fun {_} {_} hV hγ' ↦ AlternatingAnalytic.BundleRows.hloc_finiteSource k cA' hV hγ') hU hγ)
  exact ⟨AlternatingAnalytic.alternatingBundleHom_of_family (I := 𝓘(K, P)) k
    (fun {_} hU {_} hγ ↦ AlternatingAnalytic.BundleRows.glue_contMDiffOn_alternatingMapAction k
      (fun {_} {_} hV hγ' ↦ AlternatingAnalytic.BundleRows.hloc_finiteSource k cA' hV hγ') hU hγ) u v, fun _ _ ↦ rfl⟩

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
  exact AlternatingAnalytic.contMDiffVectorBundle_alternating_of_finiteCoordinates c k

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
  exact ⟨AlternatingAnalytic.alternatingBundleHom_of_finiteCoordinates c k u v, fun _ _ ↦ rfl⟩

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
  exact AlternatingAnalytic.contMDiffVectorBundle_alternating_of_family k
    (fun {_} hU {_} hγ ↦ AlternatingAnalytic.BundleRows.glue_contMDiffOn_alternatingMapAction k
      (fun {_} {_} hV hγ' ↦ AlternatingAnalytic.BundleRows.hloc_c0_retract k i r hri hV hγ') hU hγ)

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
  letI := AlternatingAnalytic.contMDiffVectorBundle_alternating_of_family (I := 𝓘(K, P)) (F₁ := A) (E₁ := E) (F₂ := B) (E₂ := F) k
    (fun {_} hU {_} hγ ↦ AlternatingAnalytic.BundleRows.glue_contMDiffOn_alternatingMapAction k
      (fun {_} {_} hV hγ' ↦ AlternatingAnalytic.BundleRows.hloc_c0_retract k i r hri hV hγ') hU hγ)
  letI := AlternatingAnalytic.contMDiffVectorBundle_alternating_of_family (I := 𝓘(K, P)) (F₁ := A') (E₁ := E') (F₂ := B') (E₂ := F') k
    (fun {_} hU {_} hγ ↦ AlternatingAnalytic.BundleRows.glue_contMDiffOn_alternatingMapAction k
      (fun {_} {_} hV hγ' ↦ AlternatingAnalytic.BundleRows.hloc_c0_retract k i r hri hV hγ') hU hγ)
  exact ⟨AlternatingAnalytic.alternatingBundleHom_of_family (I := 𝓘(K, P)) k
    (fun {_} hU {_} hγ ↦ AlternatingAnalytic.BundleRows.glue_contMDiffOn_alternatingMapAction k
      (fun {_} {_} hV hγ' ↦ AlternatingAnalytic.BundleRows.hloc_c0_retract k i r hri hV hγ') hU hγ) u v, fun _ _ ↦ rfl⟩

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
  exact AlternatingAnalytic.contMDiffVectorBundle_alternating_of_family k
    (fun {_} hU {_} hγ ↦ AlternatingAnalytic.BundleRows.glue_contMDiffOn_alternatingMapAction k
      (fun {_} {_} hV hγ' ↦ (AlternatingAnalytic.isAdmissibleOn_of_l1_retract k i r hri hγ').2) hU hγ)

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
  letI := AlternatingAnalytic.contMDiffVectorBundle_alternating_of_family (I := 𝓘(K, P)) (F₁ := A) (E₁ := E) (F₂ := B) (E₂ := F) k
    (fun {_} hU {_} hγ ↦ AlternatingAnalytic.BundleRows.glue_contMDiffOn_alternatingMapAction k
      (fun {_} {_} hV hγ' ↦ (AlternatingAnalytic.isAdmissibleOn_of_l1_retract k i r hri hγ').2) hU hγ)
  letI := AlternatingAnalytic.contMDiffVectorBundle_alternating_of_family (I := 𝓘(K, P)) (F₁ := A') (E₁ := E') (F₂ := B') (E₂ := F') k
    (fun {_} hU {_} hγ ↦ AlternatingAnalytic.BundleRows.glue_contMDiffOn_alternatingMapAction k
      (fun {_} {_} hV hγ' ↦ (AlternatingAnalytic.isAdmissibleOn_of_l1_retract k i r hri hγ').2) hU hγ)
  exact ⟨AlternatingAnalytic.alternatingBundleHom_of_family (I := 𝓘(K, P)) k
    (fun {_} hU {_} hγ ↦ AlternatingAnalytic.BundleRows.glue_contMDiffOn_alternatingMapAction k
      (fun {_} {_} hV hγ' ↦ (AlternatingAnalytic.isAdmissibleOn_of_l1_retract k i r hri hγ').2) hU hγ) u v, fun _ _ ↦ rfl⟩

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
  exact AlternatingAnalytic.contMDiffVectorBundle_alternating_of_family (I := 𝓘(K, P)) (n := (n : WithTop ℕ∞)) k
    (fun {_} hU {_} hγ ↦ AlternatingAnalytic.BundleRows.smooth_family k n hU hγ)

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
  letI := AlternatingAnalytic.contMDiffVectorBundle_alternating_of_family (I := 𝓘(K, P)) (n := (n : WithTop ℕ∞)) (F₁ := A) (E₁ := E) (F₂ := B) (E₂ := F) k
    (fun {_} hU {_} hγ ↦ AlternatingAnalytic.BundleRows.smooth_family k n hU hγ)
  letI := AlternatingAnalytic.contMDiffVectorBundle_alternating_of_family (I := 𝓘(K, P)) (n := (n : WithTop ℕ∞)) (F₁ := A') (E₁ := E') (F₂ := B') (E₂ := F') k
    (fun {_} hU {_} hγ ↦ AlternatingAnalytic.BundleRows.smooth_family k n hU hγ)
  exact ⟨AlternatingAnalytic.alternatingBundleHom_of_family (I := 𝓘(K, P)) (n := (n : WithTop ℕ∞)) k (fun {_} hU {_} hγ ↦ AlternatingAnalytic.BundleRows.smooth_family k n hU hγ) u v, fun _ _ ↦ rfl⟩
end AlternatingAnalyticChallenge.Cor4_6
