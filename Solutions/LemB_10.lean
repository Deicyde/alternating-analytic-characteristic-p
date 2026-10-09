import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Set.Finite.Basic
import AlternatingAnalytic.Algebra.OrderPattern

/-!
# Lemma B.10 (pattern homogeneity), pp. 31-32

Solution file: unlike the challenge, it additionally imports the library modules that prove
the claim. Remarks below about imports describe the challenge file.

Setting (Appendix B.3-B.4): `L` is a finite field. For a tuple `z ∈ ℕ^N` with distinct values
`y₁ < ⋯ < y_r`, its *pattern* is the map `i ↦ j` determined by `z_i = y_j` (repeated entries
are retained). "Two tuples z and z′ have the same pattern if and only if z_i < z_j ⇔ z′_i < z′_j
and z_i = z_j ⇔ z′_i = z′_j for all i, j."

Paper statement: "For every N ≥ 1 and every function T : ℕ^N → L there is an infinite H ⊆ ℕ
such that T(z) = T(z′) whenever z, z′ ∈ H^N have the same pattern."

Formalization notes:
* `ℕ^N` is `Fin N → ℕ`; `H ⊆ ℕ` is a `Set ℕ`, "infinite" is `Set.Infinite`; `z ∈ H^N` is
  `∀ i, z i ∈ H`.
* "Same pattern" is stated through the paper's own equivalent characterization: all strict
  comparisons and all equalities between coordinates agree. The rank-map definition of the
  pattern is not introduced separately.
* `L` is a finite field (`[Field L] [Finite L]`), the standing assumption of Appendix B.3; the
  proof only uses that `L` is finite. `N ≥ 1` is `hN : 1 ≤ N`.
* No library module is imported and no definitions are introduced.
-/

namespace AlternatingAnalyticChallenge.LemB_10

universe u

/-- **Lemma B.10 (pattern homogeneity).** For every `N ≥ 1` and every `T : ℕ^N → L` (`L` a finite
field) there is an infinite `H ⊆ ℕ` on which `T` depends only on the pattern of its argument. -/
theorem exists_infinite_pattern_homogeneous
    {L : Type u} [Field L] [Finite L] (N : ℕ) (hN : 1 ≤ N) (T : (Fin N → ℕ) → L) :
    ∃ H : Set ℕ, H.Infinite ∧
      ∀ z z' : Fin N → ℕ, (∀ i, z i ∈ H) → (∀ i, z' i ∈ H) →
        (∀ i j, (z i < z j ↔ z' i < z' j) ∧ (z i = z j ↔ z' i = z' j)) →
        T z = T z' := by
  exact OrderPattern.exists_infinite_order_homogeneous N T

end AlternatingAnalyticChallenge.LemB_10
