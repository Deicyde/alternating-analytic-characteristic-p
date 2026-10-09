import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Lemma B.4 (contraction), p. 28

Setting (Section B.1): `L` a field, `V` an `L`-vector space, `Λ^k V` the algebraic exterior
power, `sdim` the support dimension of Definition B.1.

Paper statement: "Let k ≥ 2 and φ = (φ₁, …, φ_{k−1}) ∈ (V*)^{k−1}. There is a linear map
c_φ : Λ^k V → V with
c_φ(x₁ ∧ ⋯ ∧ x_k) = ∑_{i=1}^k (−1)^{k+i} det (φ_a(x_b))_{1≤a≤k−1, b≠i} x_i,
and c_φ(Λ^k W) ⊆ W for every subspace W. Consequently
sdim(ω) ≥ dim span{c_φ(ω) : φ ∈ (V*)^{k−1}}."

## Formalization notes
* The degree is `k = n + 1` with `1 ≤ n`; slots are 0-indexed (`Fin (n + 1)`), and `V*` is
  the algebraic dual `Module.Dual L V`.
* `IsContraction φ c` (defined here) says that `c` satisfies the displayed formula on pure
  wedges `exteriorPower.ιMulti`. Such a map is unique.
* The lemma is split into `part1` (`c_φ` exists), `part2` (`c_φ(Λ^k W) ⊆ W`) and `part3`
  (the dimension bound, for any family `c φ` satisfying the formula).
* `part3` also asserts that the span is finite-dimensional, since `Module.finrank` is `0` on
  infinite-dimensional spaces.
* The hypothesis `1 ≤ n` is kept but not used.
* `supportedBy k W` (the image of `Λ^k W → Λ^k V`) and `sdim` (Definition B.1) are defined
  here. `sdim` is an `sInf` over a set that is never empty.
-/

namespace AlternatingAnalyticChallenge.LemB_4

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

/-- The contraction `c_φ` exists. -/
theorem part1_contraction_exists
    (L : Type*) [Field L] (V : Type*) [AddCommGroup V] [Module L V] (n : ℕ) (hn : 1 ≤ n)
    (φ : Fin n → Module.Dual L V) :
    ∃ c : (⋀[L]^(n + 1) V) →ₗ[L] V, IsContraction φ c := by
  sorry

/-- `c_φ(Λ^k W) ⊆ W` for every subspace `W`. -/
theorem part2_contraction_mem
    (L : Type*) [Field L] (V : Type*) [AddCommGroup V] [Module L V] (n : ℕ) (hn : 1 ≤ n)
    (φ : Fin n → Module.Dual L V) (c : (⋀[L]^(n + 1) V) →ₗ[L] V) (hc : IsContraction φ c)
    (W : Submodule L V) (ω : ⋀[L]^(n + 1) V) (hω : ω ∈ supportedBy (n + 1) W) :
    c ω ∈ W := by
  sorry

/-- The span of `{c_φ(ω) : φ ∈ (V*)^{k-1}}` is finite-dimensional, of dimension at most
`sdim ω`. -/
theorem part3_finrank_span_le_sdim
    (L : Type*) [Field L] (V : Type*) [AddCommGroup V] [Module L V] (n : ℕ) (hn : 1 ≤ n)
    (c : (Fin n → Module.Dual L V) → ((⋀[L]^(n + 1) V) →ₗ[L] V))
    (hc : ∀ φ, IsContraction φ (c φ)) (ω : ⋀[L]^(n + 1) V) :
    FiniteDimensional L (Submodule.span L (Set.range fun φ => c φ ω)) ∧
      Module.finrank L (Submodule.span L (Set.range fun φ => c φ ω)) ≤ sdim ω := by
  sorry

end AlternatingAnalyticChallenge.LemB_4
