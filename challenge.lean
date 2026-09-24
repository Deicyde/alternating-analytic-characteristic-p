import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.Nat.Prime.Defs

/-!
Assume universal `C^ω` regularity of the precomposition map
`f ↦ (m ↦ m ∘ (f, …, f))` on continuous alternating maps, and derive `False`.
The first challenge makes this assumption over all fields and normed spaces;
the second fixes any positive-characteristic field and degree at least its
characteristic, and only assumes it for Banach spaces with `E' = E`.

These are short consequences of the paper's counterexamples. The named Banach
assumption below is defined directly in Mathlib terms. The two proofs are intentional
challenge placeholders.
-/

open scoped ContDiff

namespace AlternatingAnalyticChallenge

universe u

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

end AlternatingAnalyticChallenge
