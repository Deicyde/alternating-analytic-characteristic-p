import AlternatingAnalytic.Analysis.RationalLaurentScalars
import AlternatingAnalytic.Category.FiniteUltrametricDomains

/-!
# Theorem H.4 (No largest full analytic domain), p. 58

Setting (Appendix H): `Vec_K` is the category of normed `K`-spaces and bounded linear maps;
`Alt^k : Vec_K^op × Vec_K → Vec_K` acts on a morphism `(u, v)` by `m ↦ v ∘ m ∘ (u, …, u)`.
"A full subcategory `𝒟 ⊆ Vec_K^op × Vec_K` is an analytic domain for `Alt^k` if the restriction of
`Alt^k` to `𝒟` is analytic on every hom space." A pair `(E, F)` is split in degree `k` if the
inclusion `Alt^k(E;F) → Mult^k(E;F)` has a bounded linear retraction.

Paper statement: "Let `p` be prime, let `k ≥ p`, and equip `K = 𝔽_p(t)` with its `t`-adic absolute
value. There is no largest full analytic domain for `Alt^k : Vec_K^op × Vec_K → Vec_K`. The
assertion remains true if the domains must be closed under isomorphisms, and if their objects are
restricted to pairs of finite-dimensional, nonarchimedean normed `K`-spaces. In the latter case,
isomorphism closure is understood inside that restricted ambient category.
More precisely, there are objects `X_k = (E_k, G)` and `Y_k = (D_k, G)` whose singleton full
subcategories are analytic, such that `Y_k` is split and the action on morphisms from `Y_k` to
`X_k` is not analytic." ("Finite-dimensional means finite algebraic dimension over the
incomplete field `K`.")

Formalization notes:
* `K = 𝔽_p(t)` with the `t`-adic absolute value is the library's
  `AlternatingAnalytic.RationalField (ZMod p) r` (imported for this definition): rational
  functions over `ZMod p` with the norm induced from the Laurent series field, `‖t‖ = r`, for a
  parameter `0 < r < 1` (all such `r` give equivalent `t`-adic absolute values; the statement is
  for every such `r`). `p` prime is `[Fact p.Prime]`.
* The category `Vec_K` is the library's `NormedSpaceCat K` (carriers in the universe of `K`,
  here `Type`), the bifunctor is the library's `alternatingFunctor K k` (index `Fin k`), hom spaces
  of `(NormedSpaceCat K)ᵒᵖ × NormedSpaceCat K` carry the library's operator norms (maximum norm on
  pairs). A full subcategory is an `ObjectProperty`, ordered by inclusion; "largest" is
  `IsGreatest` in that order. "Analytic domain" is the library predicate
  `IsAlternatingAnalyticDomain K k S` (analyticity, `AnalyticOnNhd`, of the restricted functor on
  every hom space, including hom spaces between distinct objects).
* Restricted ambient category: the library's `finiteUltrametricPairs K` (both spaces finite
  algebraic dimension over `K`, `FiniteDimensional`, and both norms ultrametric,
  `IsUltrametricDist`) and its full subcategory `FiniteUltrametricPairCat K`; analytic domains in it
  are the library's `IsFiniteUltrametricAnalyticDomain K k`, and isomorphism closure
  (`IsClosedUnderIsomorphisms`) is taken in `FiniteUltrametricPairCat K`, as the paper says.
  These are imported from `AlternatingAnalytic/Category/FiniteUltrametricDomains.lean`
  (definitions only; the theorem itself is proved in a different module).
* One theorem per variant: `part1` (no largest full analytic domain), `part2` (none among
  isomorphism-closed domains), `part3` (none in the finite-dimensional nonarchimedean ambient
  category), `part4` (none among domains of that ambient category closed under isomorphism inside
  it), and `part5` ("more precisely": the witnesses). In `part5` the shared second component
  `G` of `X_k` and `Y_k` is recorded as `X.2 = Y.2`, both witnesses are required to be
  finite-dimensional nonarchimedean pairs (as the paper's witnesses are, which the restricted
  variant uses), splitness is the in-file `IsSplitInDegree` (same as in Lemma H.3), and "not
  analytic" is `¬ AnalyticOnNhd` on the whole hom space `Y ⟶ X`.
-/

namespace AlternatingAnalyticChallenge.ThmH_4

open CategoryTheory Opposite
open scoped NNReal

/-- The pair `(E, F)` is split in degree `k`: the inclusion
`Alt^k(E;F) → Mult^k(E;F)` has a bounded linear retraction. -/
def IsSplitInDegree (K : Type*) [NontriviallyNormedField K] (k : ℕ) (E F : Type*)
    [NormedAddCommGroup E] [NormedSpace K E] [NormedAddCommGroup F] [NormedSpace K F] : Prop :=
  ∃ R : ContinuousMultilinearMap K (fun _ : Fin k => E) F →L[K] (E [⋀^Fin k]→L[K] F),
    ∀ m : E [⋀^Fin k]→L[K] F, R m.toContinuousMultilinearMap = m

/-- `Alt^k` has a largest full analytic domain. -/
def HasLargestFullAnalyticDomain (K : Type*) [NontriviallyNormedField K] (k : ℕ) : Prop :=
  ∃ S, IsGreatest {P | AlternatingAnalytic.IsAlternatingAnalyticDomain K k P} S

/-- `Alt^k` has a largest full analytic domain among those closed under isomorphisms. -/
def HasLargestIsoClosedFullAnalyticDomain (K : Type*) [NontriviallyNormedField K] (k : ℕ) :
    Prop :=
  ∃ S, IsGreatest
    {P | AlternatingAnalytic.IsAlternatingAnalyticDomain K k P ∧ P.IsClosedUnderIsomorphisms} S

/-- Inside the full subcategory of pairs of finite-dimensional nonarchimedean normed spaces,
`Alt^k` has a largest full analytic domain. -/
def HasLargestFiniteUltrametricAnalyticDomain (K : Type*) [NontriviallyNormedField K] (k : ℕ) :
    Prop :=
  ∃ S, IsGreatest {P | AlternatingAnalytic.IsFiniteUltrametricAnalyticDomain K k P} S

/-- Inside the full subcategory of pairs of finite-dimensional nonarchimedean normed spaces,
`Alt^k` has a largest full analytic domain among those closed under isomorphisms in that
subcategory. -/
def HasLargestIsoClosedFiniteUltrametricAnalyticDomain (K : Type*) [NontriviallyNormedField K]
    (k : ℕ) : Prop :=
  ∃ S, IsGreatest
    {P | AlternatingAnalytic.IsFiniteUltrametricAnalyticDomain K k P ∧
      P.IsClosedUnderIsomorphisms} S

/-- **Theorem H.4.** Over `𝔽_p(t)` with a `t`-adic absolute value and `k ≥ p`, `Alt^k` has no
largest full analytic domain. -/
theorem part1 (p k : ℕ) [Fact p.Prime] (hpk : p ≤ k)
    (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] :
    ¬ HasLargestFullAnalyticDomain (AlternatingAnalytic.RationalField (ZMod p) r) k := by
  sorry

/-- **Theorem H.4, isomorphism-closed variant.** -/
theorem part2 (p k : ℕ) [Fact p.Prime] (hpk : p ≤ k)
    (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] :
    ¬ HasLargestIsoClosedFullAnalyticDomain (AlternatingAnalytic.RationalField (ZMod p) r) k := by
  sorry

/-- **Theorem H.4, finite-dimensional nonarchimedean variant.** -/
theorem part3 (p k : ℕ) [Fact p.Prime] (hpk : p ≤ k)
    (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] :
    ¬ HasLargestFiniteUltrametricAnalyticDomain
      (AlternatingAnalytic.RationalField (ZMod p) r) k := by
  sorry

/-- **Theorem H.4, finite-dimensional nonarchimedean variant with isomorphism closure inside
the restricted ambient category.** -/
theorem part4 (p k : ℕ) [Fact p.Prime] (hpk : p ≤ k)
    (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] :
    ¬ HasLargestIsoClosedFiniteUltrametricAnalyticDomain
      (AlternatingAnalytic.RationalField (ZMod p) r) k := by
  sorry

/-- **Theorem H.4, "more precisely".** There are objects `X = (E_k, G)` and `Y = (D_k, G)`,
pairs of finite-dimensional nonarchimedean spaces, whose singleton full subcategories are
analytic domains, such that `Y` is split in degree `k` and the action of `Alt^k` on the hom
space from `Y` to `X` is not analytic. -/
theorem part5 (p k : ℕ) [Fact p.Prime] (hpk : p ≤ k)
    (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] :
    ∃ X Y : (AlternatingAnalytic.NormedSpaceCat (AlternatingAnalytic.RationalField (ZMod p) r))ᵒᵖ ×
        AlternatingAnalytic.NormedSpaceCat (AlternatingAnalytic.RationalField (ZMod p) r),
      X.2 = Y.2 ∧
      AlternatingAnalytic.finiteUltrametricPairs
        (AlternatingAnalytic.RationalField (ZMod p) r) X ∧
      AlternatingAnalytic.finiteUltrametricPairs
        (AlternatingAnalytic.RationalField (ZMod p) r) Y ∧
      AlternatingAnalytic.IsAlternatingAnalyticDomain
        (AlternatingAnalytic.RationalField (ZMod p) r) k (fun Z => Z = X) ∧
      AlternatingAnalytic.IsAlternatingAnalyticDomain
        (AlternatingAnalytic.RationalField (ZMod p) r) k (fun Z => Z = Y) ∧
      IsSplitInDegree (AlternatingAnalytic.RationalField (ZMod p) r) k Y.1.unop Y.2 ∧
      ¬ AnalyticOnNhd (AlternatingAnalytic.RationalField (ZMod p) r)
        (fun f : Y ⟶ X =>
          (AlternatingAnalytic.alternatingFunctor
            (AlternatingAnalytic.RationalField (ZMod p) r) k).map f) Set.univ := by
  sorry

end AlternatingAnalyticChallenge.ThmH_4
