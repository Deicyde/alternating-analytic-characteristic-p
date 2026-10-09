import AlternatingAnalytic.Category.NoLargestAnalyticDomain
import AlternatingAnalytic.MainTheorem
import AlternatingAnalytic.Analysis.SphericalAnalytic
import AlternatingAnalytic.Geometry.AnalyticAlternatingBundle
import AlternatingAnalytic.Geometry.AlternatingBundleShearCounterexample

set_option backward.isDefEq.respectTransparency false

/-! # Proof of the original comparator challenge

Proofs of the six statements in `challenge.lean`, from `exists_banach_counterexample_full`
(MainTheorem.lean), `contDiff_compContinuousLinearMapCLM_of_sphericallyComplete`
(Analysis/SphericalAnalytic.lean), `contMDiffVectorBundle_alternating_of_finiteCoordinates`
(Geometry/AnalyticAlternatingBundle.lean), `exists_banach_base_alternatingBundle_not_analytic`
(Geometry/AlternatingBundleShearCounterexample.lean) and
`DeterminantPair.Padding.no_largest_full_analytic_domain`
(Category/NoLargestAnalyticDomain.lean). The two general counterexamples specialize to the
Laurent field over `ZMod 2`. -/

open scoped ContDiff

namespace AlternatingAnalyticChallenge

universe u uK uE uE' uF uι uS

/-- Precomposition on degree-`k` alternating maps is `C^ω` for all Banach spaces `E`, `F`
over `K`, with `E' = E`. -/
def BanachPrecompositionAnalytic
    (K : Type u) [NontriviallyNormedField K] (k : ℕ) : Prop :=
  ∀ (E F : Type u) [NormedAddCommGroup E] [NormedSpace K E] [CompleteSpace E]
      [NormedAddCommGroup F] [NormedSpace K F] [CompleteSpace F],
      ContDiff K ω
        (fun f : E →L[K] E =>
          (ContinuousAlternatingMap.compContinuousLinearMapCLM f :
            (E [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F)))

/-- Over a nontrivially normed field of characteristic `p`, precomposition in degree `k ≥ p`
is not `C^ω` for all Banach spaces (Theorem 6.1(1)). `K` need not be complete. -/
theorem false_of_contDiff_omega_compContinuousLinearMapCLM_charP_banach
    (K : Type u) [NontriviallyNormedField K] (p k : ℕ) (hp : p.Prime)
    [CharP K p] (hpk : p ≤ k)
    (h : BanachPrecompositionAnalytic K k) : False := by
  obtain ⟨E, F, gE, gF, nE, nF, cE, cF, _, hno⟩ :=
    AlternatingAnalytic.exists_banach_counterexample_full.{u, 0} K p k hp hpk
  let : NormedAddCommGroup E := gE
  let : NormedAddCommGroup F := gF
  let : NormedSpace K E := nE
  let : NormedSpace K F := nF
  let : CompleteSpace E := cE
  let : CompleteSpace F := cF
  exact ((hno (Fin k) (by simp)).2 0).2 (h E F).contDiffAt

/-- Precomposition on continuous alternating maps is not `C^ω` for all nontrivially normed
fields, normed spaces and finite index types (Theorem 6.1(1), Corollary 6.2). -/
theorem false_of_contDiff_omega_compContinuousLinearMapCLM
    (h : ∀ (𝕜 : Type) [NontriviallyNormedField 𝕜] (E E' F : Type)
      [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
      [NormedAddCommGroup F] [NormedSpace 𝕜 F] (ι : Type) [Fintype ι],
      ContDiff 𝕜 ω
        (fun f : E →L[𝕜] E' =>
          (ContinuousAlternatingMap.compContinuousLinearMapCLM f :
            (E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)))) : False := by
  let r : NNReal := 1 / 2
  let : Fact (0 < r) := ⟨by norm_num [r]⟩
  let : Fact (r < 1) := ⟨by norm_num [r]⟩
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply false_of_contDiff_omega_compContinuousLinearMapCLM_charP_banach
    (AlternatingAnalytic.LaurentField (ZMod 2) r) 2 2 Nat.prime_two le_rfl
  intro E F _ _ _ _ _ _
  exact h (AlternatingAnalytic.LaurentField (ZMod 2) r) E E F (Fin 2)

/-- Every nonempty family of pairwise-intersecting closed balls has a common point. -/
def SphericallyComplete (F : Type uS) [PseudoMetricSpace F] : Prop :=
  ∀ S : Set (F × ℝ), S.Nonempty →
    (∀ p ∈ S, ∀ q ∈ S,
      (Metric.closedBall p.1 p.2 ∩ Metric.closedBall q.1 q.2).Nonempty) →
    (⋂ p ∈ S, Metric.closedBall p.1 p.2).Nonempty

/-- With a spherically complete ultrametric target, precomposition is `C^n` for every `n`,
including `ω` (Theorem 4.2). `K`, `E`, `E'` need not be complete, nor `E`, `E'` ultrametric. -/
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
  let : SphericallyCompleteSpace F := ⟨hF⟩
  exact ContinuousAlternatingMap.contDiff_compContinuousLinearMapCLM_of_sphericallyComplete
    (𝕜 := K) (ι := ι) (E := E) (E' := E') (F := F) (n := n)

section AnalyticAlternatingBundle

open Bundle
open scoped Bundle Manifold

/-- Over a base modelled on a space with finite coordinates `c`, the alternating-map bundle
of two analytic vector bundles is analytic (Corollary 4.6). -/
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
  exact AlternatingAnalytic.contMDiffVectorBundle_alternating_of_finiteCoordinates
    (K := K) (M := M) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂) c k

/-- The alternating-map bundle of two analytic vector bundles need not be analytic when the
field, base and fibers are unrestricted (Proposition 6.4). -/
theorem false_of_contMDiffVectorBundle_omega_alternating
    (h : ∀ (K : Type) [NontriviallyNormedField K]
      (EB HB : Type) [NormedAddCommGroup EB] [NormedSpace K EB] [TopologicalSpace HB]
      (IB : ModelWithCorners K EB HB)
      (M : Type) [TopologicalSpace M] [ChartedSpace HB M] [IsManifold IB ω M]
      (F₁ F₂ : Type) [NormedAddCommGroup F₁] [NormedSpace K F₁]
      [NormedAddCommGroup F₂] [NormedSpace K F₂]
      (E₁ E₂ : M → Type)
      [∀ x, AddCommGroup (E₁ x)] [∀ x, Module K (E₁ x)]
      [∀ x, AddCommGroup (E₂ x)] [∀ x, Module K (E₂ x)]
      [TopologicalSpace (TotalSpace F₁ E₁)] [TopologicalSpace (TotalSpace F₂ E₂)]
      [∀ x, TopologicalSpace (E₁ x)] [∀ x, TopologicalSpace (E₂ x)]
      [FiberBundle F₁ E₁] [VectorBundle K F₁ E₁]
      [FiberBundle F₂ E₂] [VectorBundle K F₂ E₂]
      [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul K (E₂ x)]
      [ContMDiffVectorBundle ω F₁ E₁ IB] [ContMDiffVectorBundle ω F₂ E₂ IB]
      (ι : Type) [Fintype ι],
      ContMDiffVectorBundle ω (F₁ [⋀^ι]→L[K] F₂)
        (fun x ↦ E₁ x [⋀^ι]→L[K] E₂ x) IB) : False := by
  let r : NNReal := 1 / 2
  let : Fact (0 < r) := ⟨by norm_num [r]⟩
  let : Fact (r < 1) := ⟨by norm_num [r]⟩
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, F, gE, gF, nE, nF, _, _, _, _, hno⟩ :=
    AlternatingAnalytic.exists_banach_base_alternatingBundle_not_analytic
      (AlternatingAnalytic.LaurentField (ZMod 2) r) 2 2 Nat.prime_two le_rfl
  let : NormedAddCommGroup E := gE
  let : NormedAddCommGroup F := gF
  let : NormedSpace (AlternatingAnalytic.LaurentField (ZMod 2) r) E := nE
  let : NormedSpace (AlternatingAnalytic.LaurentField (ZMod 2) r) F := nF
  exact hno (h (AlternatingAnalytic.LaurentField (ZMod 2) r)
    (E →L[AlternatingAnalytic.LaurentField (ZMod 2) r] E)
    (E →L[AlternatingAnalytic.LaurentField (ZMod 2) r] E)
    𝓘(AlternatingAnalytic.LaurentField (ZMod 2) r,
      E →L[AlternatingAnalytic.LaurentField (ZMod 2) r] E)
    (E →L[AlternatingAnalytic.LaurentField (ZMod 2) r] E) (E × E) F
    (AlternatingAnalytic.shearBundleCore
      (K := AlternatingAnalytic.LaurentField (ZMod 2) r) (D := E) (E := E)).Fiber
    (AlternatingAnalytic.ShearTargetBundle
      (AlternatingAnalytic.LaurentField (ZMod 2) r) E E F) (Fin 2))

end AnalyticAlternatingBundle

open scoped NNReal

/-- The degree-`k` alternating-map functor has a largest full subcategory on which it is
analytic on all hom spaces, with their operator norms. -/
def HasLargestFullAnalyticDomain
    (K : Type u) [NontriviallyNormedField K] (k : ℕ) : Prop :=
  ∃ S, IsGreatest
    {P | AlternatingAnalytic.IsAlternatingAnalyticDomain K k P} S

/-- Over `𝔽_p(t)` with `‖t‖ = r`, the degree-`k` alternating-map functor has no largest
full analytic domain when `k ≥ p` (Theorem H.4). -/
theorem no_largest_full_analytic_domain_charP
    (p k : ℕ) [Fact p.Prime] (hpk : p ≤ k)
    (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] :
    ¬ HasLargestFullAnalyticDomain
      (AlternatingAnalytic.RationalField (ZMod p) r) k := by
  rcases AlternatingAnalytic.DeterminantPair.Padding.no_largest_full_analytic_domain
      p r k hpk with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h, _⟩
  exact h

end AlternatingAnalyticChallenge
