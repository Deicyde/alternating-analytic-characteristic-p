import ChallengeDefinitions

/-!
The challenge concerns `Q(f)(m) = m ∘ (f, …, f)` on continuous alternating forms.
`BanachSpace K` bundles a complete normed vector space. `precomposition` is `Q`;
`HasBoundedLift` means that `Q` is the diagonal of a continuous multilinear map.
`HasEquivalentUltrametricNorm` means a strong-triangle-inequality seminorm with
positive two-sided bounds against the original norm.

All shared definitions are transparent and depend only on Mathlib. The field `K`
need not be complete; the Banach norms need not be ultrametric. The two proofs
below are intentional challenge placeholders.
-/

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
  sorry

/-- Alternating precomposition is analytic on every triple of Banach spaces
exactly when the degree's factorial is nonzero in the prescribed field. -/
theorem factorial_ne_zero_iff_allBanachPrecompositionAnalytic
    (K : Type u) [NontriviallyNormedField K] (k : ℕ) :
    (k.factorial : K) ≠ 0 ↔
      ∀ E E' F : BanachSpace K, ∀ f₀ : E →L[K] E',
        AnalyticAt K (precomposition K (Fin k) E E' F) f₀ := by
  sorry

end AlternatingAnalyticChallenge
