import AlternatingAnalytic.Main
import AlternatingAnalytic.Analysis.FactorialInvertible

/-! The exact factorial criterion for analyticity on all Banach spaces. -/

noncomputable section

namespace AlternatingAnalytic

open Round24Transfer

universe u

/-- Analyticity of degree-k alternating precomposition for every triple of Banach spaces. -/
def AllBanachPrecompositionAnalytic (K : Type u) [NontriviallyNormedField K] (k : ℕ) : Prop :=
  ∀ (E E' F : Type u) [NormedAddCommGroup E] [NormedAddCommGroup E']
    [NormedAddCommGroup F] [NormedSpace K E] [NormedSpace K E'] [NormedSpace K F]
    [CompleteSpace E] [CompleteSpace E'] [CompleteSpace F],
    ∀ f₀ : E →L[K] E', AnalyticAt K (Q K (Fin k) E E' F) f₀

/-- The paper's complete classification, valid for every prescribed nontrivially normed field. -/
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
