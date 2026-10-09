import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Set.Finite.Basic

/-!
# Lemma B.10 (pattern homogeneity), pp. 31-32

Setting (Appendix B.3-B.4): `L` is a finite field. For a tuple `z ∈ ℕ^N` with distinct values
`y₁ < ⋯ < y_r`, its *pattern* is the map `i ↦ j` determined by `z_i = y_j` (repeated entries
are retained). "Two tuples z and z′ have the same pattern if and only if z_i < z_j ⇔ z′_i < z′_j
and z_i = z_j ⇔ z′_i = z′_j for all i, j."

Paper statement: "For every N ≥ 1 and every function T : ℕ^N → L there is an infinite H ⊆ ℕ
such that T(z) = T(z′) whenever z, z′ ∈ H^N have the same pattern."

## Formalization notes
* `ℕ^N` is `Fin N → ℕ`, `H` is a `Set ℕ` with `H.Infinite`, and `z ∈ H^N` is `∀ i, z i ∈ H`.
* "Same pattern" is the paper's comparison characterization above; the rank map is not defined.
* `L` is a finite field as in Appendix B.3; the proof uses only that `L` is finite.
-/

namespace AlternatingAnalyticChallenge.LemB_10

universe u

/-- For every `T : ℕ^N → L` there is an infinite `H ⊆ ℕ` on which `T` depends only on the
pattern of its argument. -/
theorem exists_infinite_pattern_homogeneous
    {L : Type u} [Field L] [Finite L] (N : ℕ) (hN : 1 ≤ N) (T : (Fin N → ℕ) → L) :
    ∃ H : Set ℕ, H.Infinite ∧
      ∀ z z' : Fin N → ℕ, (∀ i, z i ∈ H) → (∀ i, z' i ∈ H) →
        (∀ i j, (z i < z j ↔ z' i < z' j) ∧ (z i = z j ↔ z' i = z' j)) →
        T z = T z' := by
  sorry

end AlternatingAnalyticChallenge.LemB_10
