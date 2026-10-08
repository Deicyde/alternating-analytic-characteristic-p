import AlternatingAnalytic.Analysis.LaurentField
import AlternatingAnalytic.Analysis.EquivalentUltrametric
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Topology.VectorBundle.ContinuousAlternatingMap
import AlternatingAnalytic.Laurent.FiniteDimSharp.IfHalf
import AlternatingAnalytic.Laurent.FiniteDimSharp.OnlyIf

/-!
# Corollary C.8 (finite dimension is sharp for nonarchimedean bases), p. 40

Solution: the statements of `Challenges/CorC_8.lean`, proved from the library
(`Laurent/FiniteDimSharp/`; the two predicates are copies of
`AlternatingAnalytic.FiniteDimSharp.PreservesAnalyticBundles` and `PreservesAnalyticMorphisms`):
* "if": `AlternatingAnalytic.FiniteDimSharp.preserves_of_finiteDimensional` (`IfHalf.lean`):
  continuous coordinates `ContinuousLinearEquiv.ofFinrankEq`, then the finite-coordinate theorems
  `contMDiffVectorBundle_alternating_of_finiteCoordinates` and
  `alternatingBundleHom_of_finiteCoordinates`;
* "only if": `AlternatingAnalytic.FiniteDimSharp.finiteDimensional_of_preserves` (`OnlyIf.lean`),
  using only morphism preservation: an infinite-dimensional `P` contains a complemented copy of
  `c₀(ℕ, K)` (`exists_cZero_retraction_of_discrete`, `Renorm.lean`: rounded norm, orthonormal
  sequence, Ingleton extension onto the spherically complete `c₀(ℕ, K)`); on trivial bundles over
  `P` the family `x ↦ D_{π x}` is an analytic section whose induced section has coordinates
  `x ↦ A(D_{π x})` (`TrivialBundleAction.lean`), contradicting Proposition C.6 at `u₀ = 0`
  (`czero_not_analyticAt_precomp`).
-/

set_option backward.isDefEq.respectTransparency false

open scoped NNReal Manifold ContDiff
open Bundle

namespace AlternatingAnalyticChallenge.CorC_8

open AlternatingAnalytic

universe u

/-- The alternating construction preserves analytic bundles over every analytic manifold
modeled on `P`, with arbitrary normed fibers. -/
def PreservesAnalyticBundles (K : Type u) [NontriviallyNormedField K]
    (P : Type u) [NormedAddCommGroup P] [NormedSpace K P] (k : ℕ) : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace P M] [IsManifold 𝓘(K, P) ω M]
    (F₁ F₂ : Type u) [NormedAddCommGroup F₁] [NormedSpace K F₁]
    [NormedAddCommGroup F₂] [NormedSpace K F₂]
    (E₁ E₂ : M → Type u)
    [∀ x, AddCommGroup (E₁ x)] [∀ x, Module K (E₁ x)]
    [∀ x, AddCommGroup (E₂ x)] [∀ x, Module K (E₂ x)]
    [TopologicalSpace (TotalSpace F₁ E₁)] [TopologicalSpace (TotalSpace F₂ E₂)]
    [∀ x, TopologicalSpace (E₁ x)] [∀ x, TopologicalSpace (E₂ x)]
    [FiberBundle F₁ E₁] [VectorBundle K F₁ E₁]
    [FiberBundle F₂ E₂] [VectorBundle K F₂ E₂]
    [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul K (E₂ x)]
    [ContMDiffVectorBundle ω F₁ E₁ 𝓘(K, P)] [ContMDiffVectorBundle ω F₂ E₂ 𝓘(K, P)],
    ContMDiffVectorBundle ω (F₁ [⋀^Fin k]→L[K] F₂)
      (fun x ↦ E₁ x [⋀^Fin k]→L[K] E₂ x) 𝓘(K, P)

/-- The alternating construction preserves operator-valued analytic morphisms: analytic
sections `u : E' → E` and `v : F → F'` induce the analytic section `m ↦ v ∘ m ∘ (u, …, u)` of the
operator bundle `Alt^k(E; F) →L Alt^k(E'; F')`. -/
def PreservesAnalyticMorphisms (K : Type u) [NontriviallyNormedField K]
    (P : Type u) [NormedAddCommGroup P] [NormedSpace K P] (k : ℕ) : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace P M] [IsManifold 𝓘(K, P) ω M]
    (A A' B B' : Type u) [NormedAddCommGroup A] [NormedSpace K A]
    [NormedAddCommGroup A'] [NormedSpace K A']
    [NormedAddCommGroup B] [NormedSpace K B]
    [NormedAddCommGroup B'] [NormedSpace K B']
    (E E' F F' : M → Type u)
    [∀ b, AddCommGroup (E b)] [∀ b, Module K (E b)] [∀ b, TopologicalSpace (E b)]
    [∀ b, AddCommGroup (E' b)] [∀ b, Module K (E' b)] [∀ b, TopologicalSpace (E' b)]
    [∀ b, AddCommGroup (F b)] [∀ b, Module K (F b)] [∀ b, TopologicalSpace (F b)]
    [∀ b, AddCommGroup (F' b)] [∀ b, Module K (F' b)] [∀ b, TopologicalSpace (F' b)]
    [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousSMul K (E b)]
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
    (u : ContMDiffSection 𝓘(K, P) (A' →L[K] A) ω (fun b ↦ E' b →L[K] E b))
    (v : ContMDiffSection 𝓘(K, P) (B →L[K] B') ω (fun b ↦ F b →L[K] F' b)),
    ∃ s : ContMDiffSection 𝓘(K, P)
        ((A [⋀^Fin k]→L[K] B) →L[K] (A' [⋀^Fin k]→L[K] B')) ω
        (fun b ↦ (E b [⋀^Fin k]→L[K] F b) →L[K] (E' b [⋀^Fin k]→L[K] F' b)),
      ∀ (b : M) (m : E b [⋀^Fin k]→L[K] F b),
        s b m = (v b).compContinuousAlternatingMap (m.compContinuousLinearMap (u b))

/-- **Corollary C.8, "if".** Over `K = 𝔽_q((u))`, a finite-dimensional `P` admits preservation of
analytic bundles and of operator-valued analytic morphisms. -/
theorem part1_of_finiteDimensional
    (κ : Type u) [Field κ] [Finite κ] (p : ℕ) (hp : p.Prime) [CharP κ p]
    (k : ℕ) (hpk : p ≤ k) (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)]
    (P : Type u) [NormedAddCommGroup P] [NormedSpace (LaurentField κ r) P] [CompleteSpace P]
    (hP : HasEquivalentUltrametricNorm (LaurentField κ r) P)
    (hfin : FiniteDimensional (LaurentField κ r) P) :
    PreservesAnalyticBundles (LaurentField κ r) P k ∧
      PreservesAnalyticMorphisms (LaurentField κ r) P k :=
  FiniteDimSharp.preserves_of_finiteDimensional (LaurentField κ r) P k

/-- **Corollary C.8, "only if".** Over `K = 𝔽_q((u))` with `k ≥ p`, if the alternating construction
preserves analytic bundles and operator-valued analytic morphisms over every analytic manifold
modeled on the Banach space `P` (with an equivalent nonarchimedean norm), then `P` is
finite-dimensional. -/
theorem part2_finiteDimensional_of_preserves
    (κ : Type u) [Field κ] [Finite κ] (p : ℕ) (hp : p.Prime) [CharP κ p]
    (k : ℕ) (hpk : p ≤ k) (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)]
    (P : Type u) [NormedAddCommGroup P] [NormedSpace (LaurentField κ r) P] [CompleteSpace P]
    (hP : HasEquivalentUltrametricNorm (LaurentField κ r) P)
    (h : PreservesAnalyticBundles (LaurentField κ r) P k ∧
      PreservesAnalyticMorphisms (LaurentField κ r) P k) :
    FiniteDimensional (LaurentField κ r) P :=
  FiniteDimSharp.finiteDimensional_of_preserves κ p hp k hpk r P hP h

end AlternatingAnalyticChallenge.CorC_8
