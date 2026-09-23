import ChallengeDefinitions

/-! Both compact challenge propositions are equivalent to the previous fully expanded
statements. Each direction only packages or unpacks Banach-space structures;
this file is independent of the challenge, solution, and proof library. -/

open scoped ContDiff

namespace AlternatingAnalyticChallenge

universe u v

/-- Bundling Banach spaces preserves the complete counterexample proposition. -/
theorem counterexample_statement_iff_unbundled
    (K : Type u) [NontriviallyNormedField K] (k : ℕ) :
    (∃ E F : BanachSpace K,
      ¬ HasEquivalentUltrametricNorm K F ∧
      ∀ (ι : Type v) [Fintype ι], Fintype.card ι = k →
        ¬ HasBoundedLift K ι E E F ∧
        ∀ f₀ : E →L[K] E,
          ¬ AnalyticAt K (precomposition K ι E E F) f₀ ∧
          ¬ ContDiffAt K ω (precomposition K ι E E F) f₀) ↔
    (∃ (E F : Type u) (normedGroupE : NormedAddCommGroup E)
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
                    (E [⋀^ι]→L[K] F) →L[K] (E [⋀^ι]→L[K] F))) f₀) := by
  constructor
  · rintro ⟨E, F, hF, h⟩
    exact ⟨E.carrier, F.carrier, E.normedAddCommGroup, F.normedAddCommGroup,
      E.normedSpace, F.normedSpace, E.completeSpace, F.completeSpace, hF, h⟩
  · rintro ⟨E, F, gE, gF, nE, nF, cE, cF, hF, h⟩
    let : NormedAddCommGroup E := gE
    let : NormedAddCommGroup F := gF
    let : NormedSpace K E := nE
    let : NormedSpace K F := nF
    let : CompleteSpace E := cE
    let : CompleteSpace F := cF
    exact ⟨BanachSpace.of (K := K) E, BanachSpace.of (K := K) F, hF, h⟩

/-- Bundling Banach spaces preserves the exact factorial classification proposition. -/
theorem factorial_classification_statement_iff_unbundled
    (K : Type u) [NontriviallyNormedField K] (k : ℕ) :
    ((k.factorial : K) ≠ 0 ↔
      ∀ E E' F : BanachSpace K, ∀ f₀ : E →L[K] E',
        AnalyticAt K (precomposition K (Fin k) E E' F) f₀) ↔
    ((k.factorial : K) ≠ 0 ↔
      ∀ (E E' F : Type u) [NormedAddCommGroup E] [NormedAddCommGroup E']
        [NormedAddCommGroup F] [NormedSpace K E] [NormedSpace K E'] [NormedSpace K F]
        [CompleteSpace E] [CompleteSpace E'] [CompleteSpace F],
        ∀ f₀ : E →L[K] E', AnalyticAt K
          (fun f : E →L[K] E' =>
            (ContinuousAlternatingMap.compContinuousLinearMapCLM
                (𝕜 := K) (F := F) (ι := Fin k) f :
              (E' [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F))) f₀) := by
  have hspaces :
      (∀ E E' F : BanachSpace K, ∀ f₀ : E →L[K] E',
        AnalyticAt K (precomposition K (Fin k) E E' F) f₀) ↔
      (∀ (E E' F : Type u) [NormedAddCommGroup E] [NormedAddCommGroup E']
        [NormedAddCommGroup F] [NormedSpace K E] [NormedSpace K E'] [NormedSpace K F]
        [CompleteSpace E] [CompleteSpace E'] [CompleteSpace F],
        ∀ f₀ : E →L[K] E', AnalyticAt K
          (fun f : E →L[K] E' =>
            (ContinuousAlternatingMap.compContinuousLinearMapCLM
                (𝕜 := K) (F := F) (ι := Fin k) f :
              (E' [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F))) f₀) := by
    constructor
    · intro h E E' F _ _ _ _ _ _ _ _ _ f₀
      exact h (BanachSpace.of (K := K) E) (BanachSpace.of (K := K) E') (BanachSpace.of (K := K) F) f₀
    · intro h E E' F f₀
      exact h E.carrier E'.carrier F.carrier f₀
  exact iff_congr Iff.rfl hspaces

end AlternatingAnalyticChallenge
