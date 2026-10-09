import AlternatingAnalytic.Category.AnalyticDomains

/-!
# Lemma H.3 (split destinations give analytic actions), p. 60

Setting (Appendix H): `Vec_K` is the category of normed `K`-spaces and bounded linear maps.
`Alt^k : Vec_K^op × Vec_K → Vec_K` sends `(E, F)` to the bounded alternating `k`-linear maps
`E^k → F`, and a morphism `(u, v)` with `u : E → D`, `v : G → F` acts by
`m ↦ v ∘ m ∘ (u, …, u)`. Hom spaces carry the operator norm, products the maximum norm.
"A full subcategory `𝒟 ⊆ Vec_K^op × Vec_K` is an analytic domain for `Alt^k` if the restriction
of `Alt^k` to `𝒟` is analytic on every hom space." "A pair `(E, F)` is split in degree `k`
if the isometric inclusion `j_{E,F} : Alt^k(E;F) → Mult^k(E;F)` has a bounded linear retraction."

Paper statement: "Every morphism-space action whose destination is a split pair is analytic. In
particular, the full subcategory of split pairs is an analytic domain."

## Formalization notes

* `IsSplitInDegree K k E F` asks for a continuous linear retraction of
  `ContinuousAlternatingMap.toContinuousMultilinearMap`, with no norm bound, as in the paper.
* `jointAction K k (u, v)` is `m ↦ v ∘ m ∘ (u, …, u)` as a continuous linear map.
* "Analytic" is `AnalyticOnNhd K _ Set.univ` on the whole hom space: a power series at every
  point. For incomplete ranges the paper's `C^ω` convention also asks for derivative regularity.
* `part1` and `part2` use the library's `NormedSpaceCat K` (carriers in the universe of `K`),
  `alternatingFunctor K k` and `IsAlternatingAnalyticDomain K k`, imported from
  `AlternatingAnalytic/Category/AnalyticDomains.lean`, the file that also proves the lemma.
  A full subcategory is an `ObjectProperty`.
* `part1_operator` is the first assertion for normed spaces in independent universes, without
  the category.
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

/-- Lemma H.3, first assertion: every morphism-space action of `Alt^k` whose destination is
a split pair is analytic. -/
theorem part1 (K : Type u) [NontriviallyNormedField K] (k : ℕ)
    (X Y : (AlternatingAnalytic.NormedSpaceCat K)ᵒᵖ × AlternatingAnalytic.NormedSpaceCat K)
    (hY : IsSplitInDegree K k Y.1.unop Y.2) :
    AnalyticOnNhd K (fun f : X ⟶ Y => (AlternatingAnalytic.alternatingFunctor K k).map f)
      Set.univ := by
  sorry

/-- Lemma H.3, first assertion, without the category: if `(E, F)` is split in degree `k`,
then `(u, v) ↦ (m ↦ v ∘ m ∘ (u, …, u))` is analytic on `L(E, D) × L(G, F)`. -/
theorem part1_operator (K : Type u) [NontriviallyNormedField K] (k : ℕ)
    (D : Type uD) (E : Type uE) (F : Type uF) (G : Type uG)
    [NormedAddCommGroup D] [NormedSpace K D] [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup F] [NormedSpace K F] [NormedAddCommGroup G] [NormedSpace K G]
    (h : IsSplitInDegree K k E F) :
    AnalyticOnNhd K (fun a : (E →L[K] D) × (G →L[K] F) => jointAction K k a) Set.univ := by
  sorry

/-- Lemma H.3, second assertion: the full subcategory of pairs split in degree `k` is an
analytic domain for `Alt^k`. -/
theorem part2 (K : Type u) [NontriviallyNormedField K] (k : ℕ) :
    AlternatingAnalytic.IsAlternatingAnalyticDomain K k
      (fun X => IsSplitInDegree K k X.1.unop X.2) := by
  sorry

end AlternatingAnalyticChallenge.LemH_3
