import AlternatingAnalytic.Analysis.LaurentResidueLift
import AlternatingAnalytic.Analysis.PrescribedLaurentBase
import AlternatingAnalytic.Analysis.BaseChangeLiftDescent
import AlternatingAnalytic.Analysis.DenseScalarLiftTransport

/-!
# Banach counterexamples in characteristic `p`

For every nontrivially normed field `K` of characteristic `p` and every `k ≥ p`, there are Banach
spaces `E`, `F` over `K` such that `F` has no equivalent ultrametric norm and the precomposition
action `A^k` is analytic nowhere (Theorem 6.1(1), proved in Appendix E). `E` and `F` are first built
over a Laurent series field over `ZMod p` (bounded sequences and a completed projective exterior
power), then base changed to the completion of `K` and restricted to `K`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped NNReal BoundedContinuousFunction

namespace AlternatingAnalytic

open LiftCriterion

universe u v

/-- The counterexample over a complete field, with a growth witness on `F` that still excludes
an equivalent ultrametric norm after restricting scalars. -/
theorem exists_completeField_counterexample
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K]
    (p k : ℕ) [Fact p.Prime] [CharP K p] (hpk : p ≤ k) :
    ∃ (E F : Type u) (normedGroupE : NormedAddCommGroup E)
      (normedGroupF : NormedAddCommGroup F),
      let : NormedAddCommGroup E := normedGroupE
      let : NormedAddCommGroup F := normedGroupF
      ∃ (normedSpaceE : NormedSpace K E) (normedSpaceF : NormedSpace K F),
        let : NormedSpace K E := normedSpaceE
        let : NormedSpace K F := normedSpaceF
        ∃ (_ : CompleteSpace E) (_ : CompleteSpace F),
          HasLinearUnitSumGrowth F ∧ ¬ HasBoundedLift K (Fin k) E E F := by
  let : IsUltrametricDist K := charP_isUltrametricDist p
  obtain ⟨r, hr0, hr1, hA⟩ := exists_sameUniverse_laurentField_normedAlgebra K p
  let : Fact (0 < r) := ⟨hr0⟩
  let : Fact (r < 1) := ⟨hr1⟩
  let κ := ULift.{u} (ZMod p)
  let K₁ := LaurentField κ r
  let : NormedAlgebra K₁ K := hA.some
  let E₁ := ℕ →ᵇ K₁
  let B := ProjectiveExteriorCompletion K₁ ℕ k
  let E := CompletedBaseChange K₁ E₁ K
  let F := CompletedBaseChange K₁ B K
  have hk : 2 ≤ k := (show p.Prime from Fact.out).two_le.trans hpk
  have hgrowth : HasLinearUnitSumGrowth B := laurentExterior_hasLinearUnitSumGrowth κ r k hk
  have hno : ¬ HasBoundedLift K₁ (Fin k) E₁ E₁ B :=
    laurent_not_hasBoundedLift κ r k p hpk
  refine ⟨E, F, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, ?_, ?_⟩
  · exact hgrowth.map (completedBaseChangeEmbedding K₁ B K).toLinearMap.toAddMonoidHom
      (completedBaseChangeEmbedding K₁ B K).isometry
  · exact not_hasBoundedLift_completedBaseChange K₁ E₁ B K k hno

/-- Theorem 6.1(1): over any nontrivially normed field of characteristic `p`, complete or not,
and for `k ≥ p`, there are Banach `E`, `F` with `F` not equivalently ultrametric and `A^k`
analytic nowhere. The same `E`, `F` work for every index type of cardinality `k`. -/
theorem exists_nowhereAnalytic_banach_counterexample
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
          ∀ f₀ : E →L[K] E,
            ¬ AnalyticAt K
              (fun f : E →L[K] E =>
                (ContinuousAlternatingMap.compContinuousLinearMapCLM
                    (𝕜 := K) (F := F) (ι := ι) f :
                  (E [⋀^ι]→L[K] F) →L[K] (E [⋀^ι]→L[K] F))) f₀ := by
  let : Fact p.Prime := ⟨hp⟩
  let L := UniformSpace.Completion K
  let : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  obtain ⟨E, F, gE, gF, nE, nF, cE, cF, hgrowth, hno⟩ :=
    exists_completeField_counterexample L p k hpk
  let : NormedAddCommGroup E := gE
  let : NormedAddCommGroup F := gF
  let : NormedSpace L E := nE
  let : NormedSpace L F := nF
  let : CompleteSpace E := cE
  let : CompleteSpace F := cF
  let : NormedSpace K E := NormedSpace.restrictScalars K L E
  let : NormedSpace K F := NormedSpace.restrictScalars K L F
  let : IsScalarTower K L E := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : IsScalarTower K L F := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  refine ⟨E, F, gE, gF, inferInstance, inferInstance, cE, cF,
    hgrowth.not_hasEquivalentUltrametricNorm K, ?_⟩
  intro ι _ hι f₀ hanalytic
  have hK : HasBoundedLift K ι E E F := hasBoundedLift_of_analyticAt hanalytic
  have hL : HasBoundedLift L ι E E F := hasBoundedLift_completion_of_base hK
  exact hno (hasBoundedLift_reindex ((Fintype.equivFin ι).trans (finCongr hι)) hL)

end AlternatingAnalytic
