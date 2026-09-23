/-
Comparator solution. The two theorem statements are copied verbatim from `challenge.lean`.
They are proved by unfolding the formalization's abbreviations in its checked theorems.
Do not import the challenge and solution together: they intentionally use the same names.
-/
import AlternatingAnalytic.MainTheorem
import AlternatingAnalytic.Analysis.FactorialClassification

open scoped ContDiff

namespace AlternatingAnalyticChallenge

universe u v

/-- For every prescribed nontrivially normed field of positive characteristic and every
degree at least that characteristic, the same Banach spaces give no bounded lift,
nowhere analytic precomposition, and nowhere `C^ω` precomposition for every finite
index type of that degree. The target admits no equivalent ultrametric norm. -/
theorem exists_banach_counterexample_full
    (K : Type u) [NontriviallyNormedField K] (p k : ℕ) (hp : p.Prime)
    [CharP K p] (hpk : p ≤ k) :
    ∃ (E F : Type u) (normedGroupE : NormedAddCommGroup E)
      (normedGroupF : NormedAddCommGroup F),
      let : NormedAddCommGroup E := normedGroupE
      let : NormedAddCommGroup F := normedGroupF
      ∃ (normedSpaceE : NormedSpace K E) (normedSpaceF : NormedSpace K F),
        let : NormedSpace K E := normedSpaceE
        let : NormedSpace K F := normedSpaceF
        ∃ (_ : CompleteSpace E) (_ : CompleteSpace F),
          (¬ ∃ q : Seminorm K F,
            (∀ x y, q (x + y) ≤ max (q x) (q y)) ∧
            (∃ C : ℝ, 0 < C ∧ ∀ x, ‖x‖ ≤ C * q x) ∧
            (∃ C : ℝ, 0 < C ∧ ∀ x, q x ≤ C * ‖x‖)) ∧
          ∀ (ι : Type v) [Fintype ι], Fintype.card ι = k →
            (¬ ∃ P : ContinuousMultilinearMap K
                (fun _ : Fin (Fintype.card ι) => E →L[K] E)
                ((E [⋀^ι]→L[K] F) →L[K] (E [⋀^ι]→L[K] F)),
              ∀ f : E →L[K] E, P (fun _ => f) =
                (ContinuousAlternatingMap.compContinuousLinearMapCLM
                    (𝕜 := K) (F := F) (ι := ι) f :
                  (E [⋀^ι]→L[K] F) →L[K] (E [⋀^ι]→L[K] F))) ∧
            ∀ f₀ : E →L[K] E,
              (¬ AnalyticAt K
                (fun f : E →L[K] E =>
                  (ContinuousAlternatingMap.compContinuousLinearMapCLM
                      (𝕜 := K) (F := F) (ι := ι) f :
                    (E [⋀^ι]→L[K] F) →L[K] (E [⋀^ι]→L[K] F))) f₀) ∧
              ¬ ContDiffAt K ω
                (fun f : E →L[K] E =>
                  (ContinuousAlternatingMap.compContinuousLinearMapCLM
                      (𝕜 := K) (F := F) (ι := ι) f :
                    (E [⋀^ι]→L[K] F) →L[K] (E [⋀^ι]→L[K] F))) f₀ := by
  simpa only [AlternatingAnalytic.HasEquivalentUltrametricNorm,
    Round24Transfer.HasBoundedLift, Round24Transfer.Q] using
    (AlternatingAnalytic.exists_banach_counterexample_full.{u, v} K p k hp hpk)

/-- Over an arbitrary prescribed nontrivially normed field, degree-`k` alternating
precomposition is analytic on every triple of Banach spaces exactly when `k!` is nonzero. -/
theorem factorial_ne_zero_iff_allBanachPrecompositionAnalytic
    (K : Type u) [NontriviallyNormedField K] (k : ℕ) :
    (k.factorial : K) ≠ 0 ↔
      ∀ (E E' F : Type u) [NormedAddCommGroup E] [NormedAddCommGroup E']
        [NormedAddCommGroup F] [NormedSpace K E] [NormedSpace K E'] [NormedSpace K F]
        [CompleteSpace E] [CompleteSpace E'] [CompleteSpace F],
        ∀ f₀ : E →L[K] E', AnalyticAt K
          (fun f : E →L[K] E' =>
            (ContinuousAlternatingMap.compContinuousLinearMapCLM
                (𝕜 := K) (F := F) (ι := Fin k) f :
              (E' [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F))) f₀ := by
  simpa only [AlternatingAnalytic.AllBanachPrecompositionAnalytic,
    Round24Transfer.Q] using
    (AlternatingAnalytic.factorial_ne_zero_iff_allBanachPrecompositionAnalytic K k)

end AlternatingAnalyticChallenge
