import AlternatingAnalytic.Main
import AlternatingAnalytic.Analysis.FactorialInvertible

/-!
# The factorial criterion

Degree-`k` alternating precomposition is analytic for all Banach spaces exactly when
`k! ≠ 0` in `K`. This is the Banach-space part of Corollary 6.2.
-/

noncomputable section

namespace AlternatingAnalytic

open LiftCriterion

universe u

/-- Degree-`k` alternating precomposition is analytic for all Banach spaces in one universe. -/
def AllBanachPrecompositionAnalytic (K : Type u) [NontriviallyNormedField K] (k : ℕ) : Prop :=
  ∀ (E E' F : Type u) [NormedAddCommGroup E] [NormedAddCommGroup E']
    [NormedAddCommGroup F] [NormedSpace K E] [NormedSpace K E'] [NormedSpace K F]
    [CompleteSpace E] [CompleteSpace E'] [CompleteSpace F],
    ∀ f₀ : E →L[K] E', AnalyticAt K (Q K (Fin k) E E' F) f₀

/-- Precomposition is analytic for all Banach spaces if and only if `k! ≠ 0` in `K`. -/
theorem factorial_ne_zero_iff_allBanachPrecompositionAnalytic
    (K : Type u) [NontriviallyNormedField K] (k : ℕ) :
    (k.factorial : K) ≠ 0 ↔ AllBanachPrecompositionAnalytic K k := by
  constructor
  · intro hk E E' F _ _ _ _ _ _ _ _ _ f₀
    exact (ContinuousAlternatingMap.cpolynomialAt_compContinuousLinearMapCLM
      (ι := Fin k) (by simpa using hk) f₀).analyticAt
  · intro h hn
    have hdiv : ringChar K ∣ k.factorial := (CharP.cast_eq_zero_iff K (ringChar K) _).mp hn
    have hp : (ringChar K).Prime := by
      apply (CharP.char_is_prime_or_zero K (ringChar K)).resolve_right
      intro hz
      rw [hz, zero_dvd_iff] at hdiv
      exact Nat.factorial_ne_zero k hdiv
    have hpk : ringChar K ≤ k := (Nat.Prime.dvd_factorial hp).mp hdiv
    obtain ⟨E, F, gE, gF, nE, nF, cE, cF, _, hno⟩ :=
      exists_nowhereAnalytic_banach_counterexample K (ringChar K) k hp hpk
    let : NormedAddCommGroup E := gE
    let : NormedAddCommGroup F := gF
    let : NormedSpace K E := nE
    let : NormedSpace K F := nF
    let : CompleteSpace E := cE
    let : CompleteSpace F := cF
    exact hno (Fin k) (by simp) 0 (h E E F 0)

end AlternatingAnalytic
