import AlternatingAnalytic.Category.AnalyticDomains
import AlternatingAnalytic.Analysis.SplitAlternatingPairs

/-!
# Lemma H.3 (split destinations give analytic actions), p. 57

Solution: the statements of `Challenges/LemH_3.lean`, from
`AlternatingAnalytic.alternatingFunctor_analyticOnNhd_hom_of_split_destination`,
`AlternatingAnalytic.splitPairs_isAnalyticDomain`
(`AlternatingAnalytic/Category/AnalyticDomains.lean`) and
`AlternatingAnalytic.analyticOnNhd_alternatingMapAction_of_split_destination`
(`AlternatingAnalytic/Analysis/SplitAlternatingPairs.lean`). The file's `IsSplitInDegree` is the
library's `IsSplitAlternatingPair` and `jointAction` the library's `alternatingMapAction`, both
definitionally.
-/

namespace AlternatingAnalyticChallenge.LemH_3

open CategoryTheory Opposite

universe u uD uE uF uG

/-- The pair `(E, F)` is split in degree `k`: the inclusion
`Alt^k(E;F) → Mult^k(E;F)` has a bounded linear retraction. -/
def IsSplitInDegree (K : Type*) [NontriviallyNormedField K] (k : ℕ) (E F : Type*)
    [NormedAddCommGroup E] [NormedSpace K E] [NormedAddCommGroup F] [NormedSpace K F] : Prop :=
  ∃ R : ContinuousMultilinearMap K (fun _ : Fin k => E) F →L[K] (E [⋀^Fin k]→L[K] F),
    ∀ m : E [⋀^Fin k]→L[K] F, R m.toContinuousMultilinearMap = m

/-- The action `m ↦ v ∘ m ∘ (u, …, u)` of `(u, v) : (E →L D) × (G →L F)`, a morphism
from `(D, G)` to `(E, F)` in `Vec_K^op × Vec_K`. -/
noncomputable def jointAction (K : Type*) [NontriviallyNormedField K] (k : ℕ)
    {D E F G : Type*} [NormedAddCommGroup D] [NormedSpace K D]
    [NormedAddCommGroup E] [NormedSpace K E] [NormedAddCommGroup F] [NormedSpace K F]
    [NormedAddCommGroup G] [NormedSpace K G] (a : (E →L[K] D) × (G →L[K] F)) :
    (D [⋀^Fin k]→L[K] G) →L[K] (E [⋀^Fin k]→L[K] F) :=
  (ContinuousLinearMap.compContinuousAlternatingMapCLM K E G F (Fin k) a.2).comp
    (ContinuousAlternatingMap.compContinuousLinearMapCLM a.1)

/-- **Lemma H.3, first assertion.** Every morphism-space action of `Alt^k` whose destination is
a split pair is analytic on the whole hom space; the source object is arbitrary. -/
theorem part1 (K : Type u) [NontriviallyNormedField K] (k : ℕ)
    (X Y : (AlternatingAnalytic.NormedSpaceCat K)ᵒᵖ × AlternatingAnalytic.NormedSpaceCat K)
    (hY : IsSplitInDegree K k Y.1.unop Y.2) :
    AnalyticOnNhd K (fun f : X ⟶ Y => (AlternatingAnalytic.alternatingFunctor K k).map f)
      Set.univ := by
  exact AlternatingAnalytic.alternatingFunctor_analyticOnNhd_hom_of_split_destination K k X Y hY

/-- **Lemma H.3, first assertion, operator form.** For arbitrary normed spaces `D, G` and a
pair `(E, F)` split in degree `k`, the joint action `(u, v) ↦ (m ↦ v ∘ m ∘ (u, …, u))` on
`L(E, D) × L(G, F)` is analytic everywhere. -/
theorem part1_operator (K : Type u) [NontriviallyNormedField K] (k : ℕ)
    (D : Type uD) (E : Type uE) (F : Type uF) (G : Type uG)
    [NormedAddCommGroup D] [NormedSpace K D] [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup F] [NormedSpace K F] [NormedAddCommGroup G] [NormedSpace K G]
    (h : IsSplitInDegree K k E F) :
    AnalyticOnNhd K (fun a : (E →L[K] D) × (G →L[K] F) => jointAction K k a) Set.univ := by
  exact AlternatingAnalytic.analyticOnNhd_alternatingMapAction_of_split_destination
    (K := K) (E := D) (E' := E) (F := G) (F' := F) k h

/-- **Lemma H.3, second assertion.** The full subcategory of pairs split in degree `k` is an
analytic domain for `Alt^k`. -/
theorem part2 (K : Type u) [NontriviallyNormedField K] (k : ℕ) :
    AlternatingAnalytic.IsAlternatingAnalyticDomain K k
      (fun X => IsSplitInDegree K k X.1.unop X.2) := by
  exact AlternatingAnalytic.splitPairs_isAnalyticDomain K k

end AlternatingAnalyticChallenge.LemH_3
