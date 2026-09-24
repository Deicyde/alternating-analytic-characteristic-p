import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Analysis.Normed.Group.Ultra

/-!
Three challenges about the precomposition map
`f ↦ (m ↦ m ∘ (f, …, f))` on continuous alternating maps.
The first two refute universal `C^ω` regularity: first over all fields and normed
spaces, then over any prescribed positive-characteristic field in degree at least
its characteristic, using Banach spaces with `E' = E`.
The third is Theorem A: a spherically complete ultrametric target gives `C^n`
precomposition for every regularity order, including `ω`.

The named Banach and spherical-completeness assumptions below are defined directly
in Mathlib terms. All three proofs are intentional challenge placeholders.
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

end AlternatingAnalyticChallenge
