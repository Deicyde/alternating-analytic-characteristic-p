import AlternatingAnalytic.Category.AnalyticDomains

/-!
# Lemma H.3 (split destinations give analytic actions), p. 57

Setting (Appendix H): `Vec_K` is the category of normed `K`-spaces and bounded linear maps over a
nontrivially normed field `K`; `Alt^k : Vec_K^op × Vec_K → Vec_K` sends `(E, F)` to the bounded
alternating `k`-linear maps `E^k → F`, and a morphism `(D, G) → (E, F)` of
`Vec_K^op × Vec_K` (that is, `u : E → D`, `v : G → F`) acts by `m ↦ v ∘ m ∘ (u, …, u)`.
Hom spaces carry the operator norm, products the maximum norm. "A full subcategory
`𝒟 ⊆ Vec_K^op × Vec_K` is an analytic domain for `Alt^k` if the restriction of `Alt^k` to `𝒟` is
analytic on every hom space." (Definition before Lemma H.3.) "A pair `(E, F)` is split in degree `k`
if the isometric inclusion `j_{E,F} : Alt^k(E;F) → Mult^k(E;F)` has a bounded linear retraction."

Paper statement: "Every morphism-space action whose destination is a split pair is analytic. In
particular, the full subcategory of split pairs is an analytic domain."

Formalization notes:
* `IsSplitInDegree K k E F` (defined here) is the existence of a continuous linear
  `R : Mult^k(E;F) → Alt^k(E;F)` with `R ∘ j = id`, where `j` is
  `ContinuousAlternatingMap.toContinuousMultilinearMap`. No norm bound on `R` is required,
  as in the paper. The degree is indexed by `Fin k`.
* `jointAction K k (u, v)` (defined here) is `m ↦ v ∘ m ∘ (u, …, u)` as a continuous linear map
  `Alt^k(D;G) →L Alt^k(E;F)`, built from Mathlib's `compContinuousLinearMapCLM` and
  `compContinuousAlternatingMapCLM`.
* "Analytic" is Mathlib's `AnalyticOnNhd K _ Set.univ` on the whole hom space (power series at
  every point). The paper's convention for `ω` on incomplete ranges also asks for derivative
  regularity; the library's notion of analytic domain uses `AnalyticOnNhd`, and so does this file.
* `part1` and `part2` are categorical, using the library's category `NormedSpaceCat K`
  (carriers in the universe of `K`), the library's bifunctor `alternatingFunctor K k`
  (its action on a morphism is `jointAction`), the library's operator norms on hom spaces of
  `(NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K` (maximum norm on pairs), and the library predicate
  `IsAlternatingAnalyticDomain K k S` (`FunctorAnalyticOnHoms` of the restriction of
  `alternatingFunctor` to the full subcategory `S`, i.e. analytic on every hom space).
  These are imported from `AlternatingAnalytic/Category/AnalyticDomains.lean`, which is also the
  file proving the lemma; it is imported only for these definitions. A full subcategory is an
  `ObjectProperty`.
* `part1_operator` is the same first assertion without the category wrapper, for arbitrary normed
  spaces in independent universes; the other object `(D, G)` is arbitrary.
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
  sorry

/-- **Lemma H.3, first assertion, operator form.** For arbitrary normed spaces `D, G` and a
pair `(E, F)` split in degree `k`, the joint action `(u, v) ↦ (m ↦ v ∘ m ∘ (u, …, u))` on
`L(E, D) × L(G, F)` is analytic everywhere. -/
theorem part1_operator (K : Type u) [NontriviallyNormedField K] (k : ℕ)
    (D : Type uD) (E : Type uE) (F : Type uF) (G : Type uG)
    [NormedAddCommGroup D] [NormedSpace K D] [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup F] [NormedSpace K F] [NormedAddCommGroup G] [NormedSpace K G]
    (h : IsSplitInDegree K k E F) :
    AnalyticOnNhd K (fun a : (E →L[K] D) × (G →L[K] F) => jointAction K k a) Set.univ := by
  sorry

/-- **Lemma H.3, second assertion.** The full subcategory of pairs split in degree `k` is an
analytic domain for `Alt^k`. -/
theorem part2 (K : Type u) [NontriviallyNormedField K] (k : ℕ) :
    AlternatingAnalytic.IsAlternatingAnalyticDomain K k
      (fun X => IsSplitInDegree K k X.1.unop X.2) := by
  sorry

end AlternatingAnalyticChallenge.LemH_3
