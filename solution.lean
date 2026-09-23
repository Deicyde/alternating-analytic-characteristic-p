import ChallengeDefinitions
import AlternatingAnalytic.MainTheorem
import AlternatingAnalytic.Analysis.FactorialClassification

/-! The two challenge statements, proved by packaging the formalization's actual
Banach witnesses. Import this module separately from `challenge`. -/

open scoped ContDiff

namespace AlternatingAnalyticChallenge

universe u v

/-- In degree at least the positive characteristic, precomposition has no bounded
multilinear lift and is nowhere analytic or `C^ω`. The same Banach spaces work for
all finite index types of that degree, and the target has no equivalent ultrametric norm. -/
theorem exists_banach_counterexample_full
    (K : Type u) [NontriviallyNormedField K] (p k : ℕ) (hp : p.Prime)
    [CharP K p] (hpk : p ≤ k) :
    ∃ E F : BanachSpace K,
      ¬ HasEquivalentUltrametricNorm K F ∧
      ∀ (ι : Type v) [Fintype ι], Fintype.card ι = k →
        ¬ HasBoundedLift K ι E E F ∧
        ∀ f₀ : E →L[K] E,
          ¬ AnalyticAt K (precomposition K ι E E F) f₀ ∧
          ¬ ContDiffAt K ω (precomposition K ι E E F) f₀ := by
  obtain ⟨E, F, gE, gF, nE, nF, cE, cF, hF, h⟩ :=
    AlternatingAnalytic.exists_banach_counterexample_full.{u, v} K p k hp hpk
  let : NormedAddCommGroup E := gE
  let : NormedAddCommGroup F := gF
  let : NormedSpace K E := nE
  let : NormedSpace K F := nF
  let : CompleteSpace E := cE
  let : CompleteSpace F := cF
  exact ⟨BanachSpace.of (K := K) E, BanachSpace.of (K := K) F, hF, h⟩

/-- Alternating precomposition is analytic on every triple of Banach spaces
exactly when the degree's factorial is nonzero in the prescribed field. -/
theorem factorial_ne_zero_iff_allBanachPrecompositionAnalytic
    (K : Type u) [NontriviallyNormedField K] (k : ℕ) :
    (k.factorial : K) ≠ 0 ↔
      ∀ E E' F : BanachSpace K, ∀ f₀ : E →L[K] E',
        AnalyticAt K (precomposition K (Fin k) E E' F) f₀ := by
  constructor
  · intro hk E E' F f₀
    exact (AlternatingAnalytic.factorial_ne_zero_iff_allBanachPrecompositionAnalytic K k).mp
      hk E.carrier E'.carrier F.carrier f₀
  · intro h
    apply (AlternatingAnalytic.factorial_ne_zero_iff_allBanachPrecompositionAnalytic K k).mpr
    intro E E' F _ _ _ _ _ _ _ _ _ f₀
    exact h (BanachSpace.of (K := K) E) (BanachSpace.of (K := K) E') (BanachSpace.of (K := K) F) f₀

end AlternatingAnalyticChallenge
