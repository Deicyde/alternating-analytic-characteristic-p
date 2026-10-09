import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Proposition B.5 (canonical exterior support), p. 30

Paper statement: "Let L be any field, V an L-vector space, k ≥ 2, and ω ∈ Λ^k V. Then
S(ω) := span{c_φ(ω) : φ ∈ (V*)^{k−1}}
is the unique smallest subspace supporting ω. In particular, ω ∈ Λ^k S(ω) and
sdim(ω) = dim S(ω)."  Here `c_φ` is the contraction of Lemma B.4.

## Formalization notes
* The degree is `k = n + 1` with `1 ≤ n`; slots are 0-indexed (`Fin (n + 1)`), and `V*` is
  the algebraic dual `Module.Dual L V`.
* `IsContraction φ c` (defined here) says that `c` satisfies the formula of Lemma B.4 on pure
  wedges; such a map exists by `LemB_4.part1_contraction_exists` and is unique.
* `S(ω)` is `Submodule.span L (Set.range fun φ => c φ ω)` for any family `c` satisfying the
  formula.
* "Unique smallest subspace supporting ω" is `part1` (`S(ω)` supports `ω`) and `part2`
  (`W` supports `ω` iff `S(ω) ≤ W`). `part3` says `S(ω)` is finite-dimensional and
  `sdim ω = finrank S(ω)`.
* The hypothesis `1 ≤ n` is kept but not used.
* `supportedBy k W` (the image of `Λ^k W → Λ^k V`) and `sdim` (Definition B.1) are defined
  here. `sdim` is an `sInf` over a set that is never empty.
* The degree-zero and degree-one remarks after the proposition are not formalized.
-/

namespace AlternatingAnalyticChallenge.PropB_5

variable {L : Type*} [Field L] {V : Type*} [AddCommGroup V] [Module L V]

/-- The image of `Λ^k W` in `Λ^k V` (Section B.1); `ω` lies in it when `W` supports `ω`. -/
noncomputable def supportedBy (k : ℕ) (W : Submodule L V) : Submodule L (⋀[L]^k V) :=
  LinearMap.range (exteriorPower.map k W.subtype)

/-- The support dimension of Definition B.1:
`sdim ω = min {dim W : W ⊆ V finite-dimensional, ω ∈ Λ^k W}`. -/
noncomputable def sdim {k : ℕ} (ω : ⋀[L]^k V) : ℕ :=
  sInf {n : ℕ | ∃ W : Submodule L V, FiniteDimensional L W ∧ ω ∈ supportedBy k W ∧
    Module.finrank L W = n}

/-- `c` is the contraction `c_φ : Λ^k V → V` of Lemma B.4 for `k = n + 1`:
`c_φ(x₁ ∧ ⋯ ∧ x_k) = ∑ᵢ (-1)^(k+i) det (φ_a(x_b))_{1 ≤ a ≤ k-1, b ≠ i} xᵢ` on pure wedges.
With 0-indexed `i : Fin (n + 1)` the sign is `(-1)^(n + i)`, and the columns `b ≠ i`, in
increasing order, are `i.succAbove b` for `b : Fin n`. -/
def IsContraction {n : ℕ} (φ : Fin n → Module.Dual L V) (c : (⋀[L]^(n + 1) V) →ₗ[L] V) :
    Prop :=
  ∀ x : Fin (n + 1) → V,
    c (exteriorPower.ιMulti L (n + 1) x) =
      ∑ i : Fin (n + 1),
        ((-1 : L) ^ (n + i.val) * Matrix.det (fun a b : Fin n => φ a (x (i.succAbove b)))) • x i

/-- `ω ∈ Λ^k S(ω)`. -/
theorem part1_mem_supportedBy_span
    (L : Type*) [Field L] (V : Type*) [AddCommGroup V] [Module L V] (n : ℕ) (hn : 1 ≤ n)
    (c : (Fin n → Module.Dual L V) → ((⋀[L]^(n + 1) V) →ₗ[L] V))
    (hc : ∀ φ, IsContraction φ (c φ)) (ω : ⋀[L]^(n + 1) V) :
    ω ∈ supportedBy (n + 1) (Submodule.span L (Set.range fun φ => c φ ω)) := by
  sorry

/-- `S(ω)` is the smallest subspace supporting `ω`. -/
theorem part2_supportedBy_iff_span_le
    (L : Type*) [Field L] (V : Type*) [AddCommGroup V] [Module L V] (n : ℕ) (hn : 1 ≤ n)
    (c : (Fin n → Module.Dual L V) → ((⋀[L]^(n + 1) V) →ₗ[L] V))
    (hc : ∀ φ, IsContraction φ (c φ)) (ω : ⋀[L]^(n + 1) V) (W : Submodule L V) :
    ω ∈ supportedBy (n + 1) W ↔ Submodule.span L (Set.range fun φ => c φ ω) ≤ W := by
  sorry

/-- `S(ω)` is finite-dimensional and `sdim ω = dim S(ω)`. -/
theorem part3_sdim_eq_finrank_span
    (L : Type*) [Field L] (V : Type*) [AddCommGroup V] [Module L V] (n : ℕ) (hn : 1 ≤ n)
    (c : (Fin n → Module.Dual L V) → ((⋀[L]^(n + 1) V) →ₗ[L] V))
    (hc : ∀ φ, IsContraction φ (c φ)) (ω : ⋀[L]^(n + 1) V) :
    FiniteDimensional L (Submodule.span L (Set.range fun φ => c φ ω)) ∧
      sdim ω = Module.finrank L (Submodule.span L (Set.range fun φ => c φ ω)) := by
  sorry

end AlternatingAnalyticChallenge.PropB_5
