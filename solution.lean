import AlternatingAnalytic.Category.NoLargestAnalyticDomain
import AlternatingAnalytic.MainTheorem
import AlternatingAnalytic.Analysis.SphericalAnalytic
import AlternatingAnalytic.Geometry.AnalyticAlternatingBundle

set_option backward.isDefEq.respectTransparency false

/-! The two contradiction challenges are proved from the actual Banach counterexample.
The prescribed-field result is proved first, then specialized to a characteristic-two
Laurent field for the global statement. The third challenge is Theorem A, proved from
the existing spherical-completeness and retraction development. The fourth challenge
exports the actual analytic alternating-bundle instance over finite-coordinate bases.
The fifth exports the nonexistence of a largest full analytic domain over the
`t`-adic rational field in degrees at least its characteristic.
Import this module separately from `challenge`. -/

open scoped ContDiff

namespace AlternatingAnalyticChallenge

universe u uK uE uE' uF uι uS

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
  obtain ⟨E, F, gE, gF, nE, nF, cE, cF, _, hno⟩ :=
    AlternatingAnalytic.exists_banach_counterexample_full.{u, 0} K p k hp hpk
  let : NormedAddCommGroup E := gE
  let : NormedAddCommGroup F := gF
  let : NormedSpace K E := nE
  let : NormedSpace K F := nF
  let : CompleteSpace E := cE
  let : CompleteSpace F := cF
  exact ((hno (Fin k) (by simp)).2 0).2 (h E F).contDiffAt

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
  let r : NNReal := 1 / 2
  let : Fact (0 < r) := ⟨by norm_num [r]⟩
  let : Fact (r < 1) := ⟨by norm_num [r]⟩
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply false_of_contDiff_omega_compContinuousLinearMapCLM_charP_banach
    (AlternatingAnalytic.LaurentField (ZMod 2) r) 2 2 Nat.prime_two le_rfl
  intro E F _ _ _ _ _ _
  exact h (AlternatingAnalytic.LaurentField (ZMod 2) r) E E F (Fin 2)

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
  let : SphericallyCompleteSpace F := ⟨hF⟩
  exact ContinuousAlternatingMap.contDiff_compContinuousLinearMapCLM_of_sphericallyComplete
    (𝕜 := K) (ι := ι) (E := E) (E' := E') (F := F) (n := n)

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
  exact AlternatingAnalytic.contMDiffVectorBundle_alternating_of_finiteCoordinates
    (K := K) (M := M) (F₁ := F₁) (F₂ := F₂) (E₁ := E₁) (E₂ := E₂) c k

end AnalyticAlternatingBundle

open scoped NNReal

/-- The degree-`k` alternating-map functor has a largest full analytic domain:
one full subcategory contains every full subcategory on which the functor is
analytic on all morphism spaces, with their canonical operator norms. -/
def HasLargestFullAnalyticDomain
    (K : Type u) [NontriviallyNormedField K] (k : ℕ) : Prop :=
  ∃ S, IsGreatest
    {P | AlternatingAnalytic.IsAlternatingAnalyticDomain K k P} S

/-- **Main Theorem (4).** Over the `t`-adic rational field `𝔽_p(t)`, the degree-`k`
alternating-map functor has no largest full analytic domain when `k ≥ p`.
Here `0 < r < 1` is the norm of `t`; this scalar field is incomplete. -/
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
