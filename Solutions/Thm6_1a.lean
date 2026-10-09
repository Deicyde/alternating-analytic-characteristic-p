import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Algebra.CharP.Defs
import AlternatingAnalytic.Analysis.EquivalentUltrametric
import AlternatingAnalytic.MainTheorem

/-!
# Proof of Theorem 6.1(1)

Specializes `exists_banach_counterexample_full` (`MainTheorem.lean`) to the index type `Fin k`.
-/

namespace AlternatingAnalyticChallenge.Thm6_1a

universe u

/-- Theorem 6.1(1): in characteristic `p > 0` and degree `k ≥ p` there are Banach `E`, `F`
with `A^k_{E,E;F}` analytic at no point and `F` without an equivalent nonarchimedean norm. -/
theorem exists_banach_nowhere_analytic_precomposition
    (K : Type u) [NontriviallyNormedField K] (p k : ℕ) [CharP K p] (hp : 0 < p)
    (hpk : p ≤ k) :
    ∃ (E F : Type u) (_ : NormedAddCommGroup E) (_ : NormedSpace K E) (_ : CompleteSpace E)
      (_ : NormedAddCommGroup F) (_ : NormedSpace K F) (_ : CompleteSpace F),
      (∀ u₀ : E →L[K] E,
        ¬ AnalyticAt K
          (fun u : E →L[K] E =>
            (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
              (E [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F))) u₀) ∧
      ¬ AlternatingAnalytic.HasEquivalentUltrametricNorm K F := by
  have hprime : p.Prime := (CharP.char_is_prime_or_zero K p).resolve_right (by omega)
  obtain ⟨E, F, gE, gF, nE, nF, cE, cF, hF, hA⟩ :=
    AlternatingAnalytic.exists_banach_counterexample_full.{u, 0} K p k hprime hpk
  refine ⟨E, F, gE, nE, cE, gF, nF, cF, fun u₀ => ((hA (Fin k) (by simp)).2 u₀).1, hF⟩

end AlternatingAnalyticChallenge.Thm6_1a
