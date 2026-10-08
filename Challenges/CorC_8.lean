import AlternatingAnalytic.Analysis.LaurentField
import AlternatingAnalytic.Analysis.EquivalentUltrametric
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Topology.VectorBundle.ContinuousAlternatingMap

/-!
# Corollary C.8 (finite dimension is sharp for nonarchimedean bases), p. 40

Paper statement (Appendix C, §C.6, `Corollary C.8`): Let `K = 𝔽_q((u))`, where `q` is a power of
`p`, with a `u`-adic absolute value, and let `k ≥ p`. Let `P` be a `K`-Banach space admitting an
equivalent nonarchimedean norm. The alternating construction preserves analytic bundles and their
operator-valued analytic morphisms over every analytic manifold modeled on `P`, with arbitrary
normed fibers, if and only if `P` is finite-dimensional.

## Formalization notes
* `K = 𝔽_q((u))` with a `u`-adic absolute value is `AlternatingAnalytic.LaurentField κ r` for a
  finite field `κ` of characteristic `p` (`[Finite κ]`, `p.Prime`, `[CharP κ p]`; a finite field of
  characteristic `p` has `q = p^n` elements) and `|u| = r ∈ (0, 1)`.
* "`K`-Banach space admitting an equivalent nonarchimedean norm": `[CompleteSpace P]` and the
  library's `HasEquivalentUltrametricNorm K P` (a seminorm satisfying the ultrametric inequality,
  two-sided equivalent to `‖·‖`), imported from `EquivalentUltrametric.lean` for this definition.
* "Analytic manifold modeled on `P`" is `[ChartedSpace P M] [IsManifold 𝓘(K, P) ω M]` (open-chart
  manifolds without boundary, as in the paper's Corollary 4.6); "analytic bundle with normed fiber"
  is a Mathlib `ContMDiffVectorBundle ω F E 𝓘(K, P)` with normed model fiber `F`.
* `PreservesAnalyticBundles K P k` (introduced here): for all such `M` and all analytic bundles
  `E₁, E₂` with normed model fibers `F₁, F₂`, the bundle `x ↦ Alt^k(E₁ x; E₂ x)` with Mathlib's
  topology on continuous alternating maps is `ContMDiffVectorBundle ω` with fiber
  `F₁ [⋀^Fin k]→L[K] F₂`.
* `PreservesAnalyticMorphisms K P k` (introduced here): for analytic bundles `E, E', F, F'` and
  analytic operator-valued sections `u : E' → E`, `v : F → F'` (Mathlib `ContMDiffSection`s of the
  `→L` bundles), the induced fiberwise map `m ↦ v_b ∘ m ∘ (u_b, …, u_b)` is an analytic section of
  the operator bundle `Alt^k(E; F) →L Alt^k(E'; F')`.
* Universes: `κ`, `P`, the base manifolds, model fibers and fibers all live in `Type u`
  (the paper's "arbitrary normed fibers" is read within one universe).
* Degree: index type `Fin k`.
* The equivalence is split into its two implications, `part1_of_finiteDimensional` ("if") and
  `part2_finiteDimensional_of_preserves` ("only if").
* Status: the "if" half follows from the library's finite-coordinate bundle theorems
  `contMDiffVectorBundle_alternating_of_finiteCoordinates` (`Geometry/AnalyticAlternatingBundle.lean`)
  and `alternatingBundleHom_of_finiteCoordinates` (`Geometry/AnalyticAlternatingBundleMorphism.lean`)
  plus continuous coordinates on a finite-dimensional space (paper Lemma A.3; Mathlib), but this
  assembly is not in the library (a check proved `part1_of_finiteDimensional` in about 8 lines:
  `ContinuousLinearEquiv.ofFinrankEq (by simp)`, then the two theorems above, with the morphism
  part closed by `rfl`); the "only if" half (via Serre's orthonormal-basis theorem and
  Proposition C.6) is not formalized.
* `set_option backward.isDefEq.respectTransparency false` (as in the library) is needed for
  instance search on `ℕ →ᵇ K₁`; it does not change any statement.
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
      PreservesAnalyticMorphisms (LaurentField κ r) P k := by
  sorry

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
    FiniteDimensional (LaurentField κ r) P := by
  sorry

end AlternatingAnalyticChallenge.CorC_8
