import AlternatingAnalytic.Analysis.RationalLaurentScalars
import AlternatingAnalytic.Category.FiniteUltrametricDomains
import AlternatingAnalytic.Category.NoLargestAnalyticDomain

/-!
# Proof of Theorem H.4

Uses `AlternatingAnalytic.DeterminantPair.Padding.no_largest_full_analytic_domain`
(`AlternatingAnalytic/Category/NoLargestAnalyticDomain.lean`), with witnesses
`objectX p r (k - p)` and `objectY p r (k - p)`.
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

/-- Theorem H.4: over `𝔽_p(t)` with a `t`-adic absolute value and `k ≥ p`, `Alt^k` has no
largest full analytic domain. -/
theorem part1 (p k : ℕ) [Fact p.Prime] (hpk : p ≤ k)
    (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] :
    ¬ HasLargestFullAnalyticDomain (AlternatingAnalytic.RationalField (ZMod p) r) k := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h, -, -, -⟩ :=
    AlternatingAnalytic.DeterminantPair.Padding.no_largest_full_analytic_domain p r k hpk
  exact h

/-- Theorem H.4: there is no largest isomorphism-closed full analytic domain. -/
theorem part2 (p k : ℕ) [Fact p.Prime] (hpk : p ≤ k)
    (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] :
    ¬ HasLargestIsoClosedFullAnalyticDomain (AlternatingAnalytic.RationalField (ZMod p) r) k := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -, -⟩ :=
    AlternatingAnalytic.DeterminantPair.Padding.no_largest_full_analytic_domain p r k hpk
  exact h

/-- Theorem H.4: there is no largest full analytic domain among pairs of finite-dimensional
nonarchimedean spaces. -/
theorem part3 (p k : ℕ) [Fact p.Prime] (hpk : p ≤ k)
    (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] :
    ¬ HasLargestFiniteUltrametricAnalyticDomain
      (AlternatingAnalytic.RationalField (ZMod p) r) k := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ :=
    AlternatingAnalytic.DeterminantPair.Padding.no_largest_full_analytic_domain p r k hpk
  exact h

/-- Theorem H.4: there is no largest full analytic domain among pairs of finite-dimensional
nonarchimedean spaces that is closed under isomorphisms in that category. -/
theorem part4 (p k : ℕ) [Fact p.Prime] (hpk : p ≤ k)
    (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] :
    ¬ HasLargestIsoClosedFiniteUltrametricAnalyticDomain
      (AlternatingAnalytic.RationalField (ZMod p) r) k := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h⟩ :=
    AlternatingAnalytic.DeterminantPair.Padding.no_largest_full_analytic_domain p r k hpk
  exact h

/-- Theorem H.4, witnesses: there are pairs `X = (E_k, G)` and `Y = (D_k, G)` of
finite-dimensional nonarchimedean spaces whose singletons are analytic domains, such that `Y`
is split in degree `k` and the action of `Alt^k` on `Y ⟶ X` is not analytic. -/
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
  obtain ⟨-, hX, hY, hsX, hsY, -, -, hsplit, -, hbad, -⟩ :=
    AlternatingAnalytic.DeterminantPair.Padding.no_largest_full_analytic_domain p r k hpk
  exact ⟨AlternatingAnalytic.DeterminantPair.Padding.objectX p r (k - p),
    AlternatingAnalytic.DeterminantPair.Padding.objectY p r (k - p), rfl, hX, hY, hsX, hsY,
    hsplit, fun h => hbad (h _ (Set.mem_univ _))⟩

end AlternatingAnalyticChallenge.ThmH_4
