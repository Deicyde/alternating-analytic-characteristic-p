import AlternatingAnalytic.Main

/-! The complete bundled main theorem: the Banach counterexample has no bounded
lift, is nowhere analytic, and is nowhere `C^ω`, for every finite index type of
the prescribed degree. The witnesses are the existing explicit construction. -/

open scoped ContDiff

namespace AlternatingAnalytic

universe u v

/-- The full main theorem of `charp.tex`, including its bounded-lift and `C^ω`
formulations. The prescribed field need not be complete, and the same Banach
spaces work for every finite index type of cardinality `k`. -/
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
          ¬ HasEquivalentUltrametricNorm K F ∧
          ∀ (ι : Type v) [Fintype ι], Fintype.card ι = k →
            ¬ Round24Transfer.HasBoundedLift K ι E E F ∧
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
  obtain ⟨E, F, gE, gF, nE, nF, cE, cF, hF, hA⟩ :=
    exists_nowhereAnalytic_banach_counterexample.{u, v} K p k hp hpk
  let : NormedAddCommGroup E := gE
  let : NormedAddCommGroup F := gF
  let : NormedSpace K E := nE
  let : NormedSpace K F := nF
  let : CompleteSpace E := cE
  let : CompleteSpace F := cF
  refine ⟨E, F, gE, gF, nE, nF, cE, cF, hF, ?_⟩
  intro ι _ hι
  refine ⟨?_, fun f₀ => ⟨hA ι hι f₀, fun h => hA ι hι f₀ h.analyticAt⟩⟩
  rintro ⟨P, hP⟩
  exact hA ι hι 0 (Round24Transfer.cpolynomialAt_of_lift P hP 0).analyticAt

end AlternatingAnalytic
