import Mathlib.Data.List.Infix
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Set.Lattice.Indexed
import AlternatingAnalytic.Scalar.ChainGap

/-!
# Lemma F.3 (chain gap), pp. 50-51

Solution: the statements of `Challenges/LemF_3.lean`, proved from the library:
* part 1: `AlternatingAnalytic.ChainGap.labelChain_inter_subsingleton`;
* part 2: `AlternatingAnalytic.ChainGap.iInter_nonempty_of_cofinite_on_chains`, via
  `AlternatingAnalytic.ChainGap.exists_extension_forall_mem`
(`Scalar/ChainGap.lean`). The library's `IsLabelChain` unfolds to the definition below.
-/

namespace AlternatingAnalyticChallenge.LemF_3

universe u

/-- A `j`-chain in the word tree `List L`: the set of words of a sequence `s₀, s₁, …` with
`s_r j ⪯ s_{r+1}` (prefix order) for every `r`. -/
def IsLabelChain {L : Type u} (j : L) (T : Set (List L)) : Prop :=
  ∃ s : ℕ → List L, (∀ r, s r ++ [j] <+: s (r + 1)) ∧ T = Set.range s

/-- **Lemma F.3, part 1.** Chains with different labels have at most one common word. -/
theorem labelChain_inter_subsingleton
    {L : Type u} [Fintype L] [Nonempty L] {j h : L} (hjh : j ≠ h)
    {T T' : Set (List L)} (hT : IsLabelChain j T) (hT' : IsLabelChain h T') :
    (T ∩ T').Subsingleton := by
  exact AlternatingAnalytic.ChainGap.labelChain_inter_subsingleton hjh hT hT'

/-- **Lemma F.3, part 2 (chain gap).** If, for each label `j`, the set `a j` contains all but
finitely many words of every `j`-chain, then the sets `a j` have a common word. -/
theorem iInter_nonempty_of_cofinite_on_chains
    {L : Type u} [Fintype L] [Nonempty L] (a : L → Set (List L))
    (ha : ∀ j : L, ∀ T : Set (List L), IsLabelChain j T → (T \ a j).Finite) :
    (⋂ j, a j).Nonempty := by
  exact AlternatingAnalytic.ChainGap.iInter_nonempty_of_cofinite_on_chains a ha

end AlternatingAnalyticChallenge.LemF_3
