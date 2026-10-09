import Mathlib.Data.List.Infix
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Set.Lattice.Indexed

/-!
# Lemma F.3 (chain gap), p. 52

Paper setting: "Let L be a nonempty finite set and Λ = L^{<ω} the set of finite words in L,
including the empty word. Write s ⪯ t when t extends s, and write sj for the word obtained by
appending j ∈ L. A j-chain is a set T = {s_0, s_1, …} with s_r j ⪯ s_{r+1} for every r. Let Γ_j
denote all such chains."

Paper statement: "Chains with different labels have at most one common word. If sets
a_j ⊆ Λ, j ∈ L, contain all but finitely many words of every chain in Γ_j, then
⋂_{j ∈ L} a_j ≠ ∅."

## Formalization notes

* `L` has `[Fintype L]` and `[Nonempty L]`; `Λ` is `List L`, with the empty word `[]`.
* `s ⪯ t` is the prefix relation `s <+: t`; the word `sj` is `s ++ [j]`.
* A `j`-chain is the range of a sequence `s : ℕ → List L` with `s r ++ [j] <+: s (r + 1)`
  (`IsLabelChain`, defined here). Such a sequence is injective, so its range is the paper's set.
* Part 1: "at most one common word" is `Set.Subsingleton` of the intersection. It does not need
  `L` finite or nonempty; the paper's standing hypotheses are kept.
* Part 2: "contains all but finitely many words of `T`" is `(T \ a j).Finite`.
-/

namespace AlternatingAnalyticChallenge.LemF_3

universe u

/-- `T` is a `j`-chain: the set of words of a sequence `s₀, s₁, …` with `s_r j ⪯ s_{r+1}` in the
prefix order. -/
def IsLabelChain {L : Type u} (j : L) (T : Set (List L)) : Prop :=
  ∃ s : ℕ → List L, (∀ r, s r ++ [j] <+: s (r + 1)) ∧ T = Set.range s

/-- Lemma F.3, part 1: chains with different labels have at most one common word. -/
theorem labelChain_inter_subsingleton
    {L : Type u} [Fintype L] [Nonempty L] {j h : L} (hjh : j ≠ h)
    {T T' : Set (List L)} (hT : IsLabelChain j T) (hT' : IsLabelChain h T') :
    (T ∩ T').Subsingleton := by
  sorry

/-- Lemma F.3, part 2: if each `a j` contains all but finitely many words of every `j`-chain, then
the sets `a j` have a common word. -/
theorem iInter_nonempty_of_cofinite_on_chains
    {L : Type u} [Fintype L] [Nonempty L] (a : L → Set (List L))
    (ha : ∀ j : L, ∀ T : Set (List L), IsLabelChain j T → (T \ a j).Finite) :
    (⋂ j, a j).Nonempty := by
  sorry

end AlternatingAnalyticChallenge.LemF_3
