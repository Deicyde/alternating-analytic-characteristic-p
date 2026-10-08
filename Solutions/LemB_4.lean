import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import AlternatingAnalytic.Algebra.ExteriorContraction

/-!
# Lemma B.4 (contraction), p. 27

Setting (Section B.1): `L` a field, `V` an `L`-vector space, `Λ^k V` the algebraic exterior
power, `sdim` the support dimension of Definition B.1.

Paper statement: "Let k ≥ 2 and φ = (φ₁, …, φ_{k−1}) ∈ (V*)^{k−1}. There is a linear map
c_φ : Λ^k V → V with
c_φ(x₁ ∧ ⋯ ∧ x_k) = ∑_{i=1}^k (−1)^{k+i} det (φ_a(x_b))_{1≤a≤k−1, b≠i} x_i,
and c_φ(Λ^k W) ⊆ W for every subspace W. Consequently
sdim(ω) ≥ dim span{c_φ(ω) : φ ∈ (V*)^{k−1}}."

Formalization notes:
* The degree is written `k = n + 1` with hypothesis `1 ≤ n` (that is, `k ≥ 2`); slots are
  0-indexed (`Fin (n + 1)`), and `V*` is the algebraic dual `Module.Dual L V`.
* `IsContraction φ c` (defined in this file) says that the linear map `c` satisfies the
  displayed formula on pure wedges `exteriorPower.ιMulti`; such a map is unique because
  pure wedges span `Λ^k V`.
* The lemma is split into `part1` (existence of `c_φ`), `part2` (`c_φ(Λ^k W) ⊆ W` for any
  map with the formula) and `part3` (the dimension bound, for any choice of maps `c φ` with
  the formula). Part 3 also asserts that the span is finite-dimensional: the paper's
  inequality implies this, and without it the `Module.finrank` bound would be vacuous on an
  infinite-dimensional span (where `finrank = 0`).
* The library proves the lemma for every `n`, including `n = 0`; the hypothesis `1 ≤ n` is
  kept for faithfulness to the paper and is unused.
* `supportedBy k W` (the image of `Λ^k W → Λ^k V`) and `sdim` (Definition B.1, as an
  `sInf` over dimensions of finite-dimensional supporting subspaces) are defined in this
  file in Mathlib terms. `sInf ∅ = 0` cannot occur, since every exterior vector has a
  finite-dimensional supporting subspace.
-/

namespace AlternatingAnalyticChallenge.LemB_4

variable {L : Type*} [Field L] {V : Type*} [AddCommGroup V] [Module L V]

/-- `Λ^k W`, regarded as a subspace of `Λ^k V`: the image of the map induced by the
inclusion `W → V` (Section B.1). Membership of `ω` means that `W` supports `ω`. -/
noncomputable def supportedBy (k : ℕ) (W : Submodule L V) : Submodule L (⋀[L]^k V) :=
  LinearMap.range (exteriorPower.map k W.subtype)

/-- **Definition B.1.** The support dimension
`sdim ω = min {dim W : W ⊆ V finite-dimensional, ω ∈ Λ^k W}`. -/
noncomputable def sdim {k : ℕ} (ω : ⋀[L]^k V) : ℕ :=
  sInf {n : ℕ | ∃ W : Submodule L V, FiniteDimensional L W ∧ ω ∈ supportedBy k W ∧
    Module.finrank L W = n}

/-- `c` is the contraction `c_φ : Λ^k V → V` of Lemma B.4 for `k = n + 1`: on pure wedges
`c_φ(x₁ ∧ ⋯ ∧ x_k) = ∑ᵢ (-1)^(k+i) det (φ_a(x_b))_{1 ≤ a ≤ k-1, b ≠ i} xᵢ`.
With 0-indexed `i : Fin (n + 1)` the sign `(-1)^(k + (i+1))` is `(-1)^(n + i)`, and the
columns `b ≠ i`, in increasing order, are `i.succAbove b` for `b : Fin n`. -/
def IsContraction {n : ℕ} (φ : Fin n → Module.Dual L V) (c : (⋀[L]^(n + 1) V) →ₗ[L] V) :
    Prop :=
  ∀ x : Fin (n + 1) → V,
    c (exteriorPower.ιMulti L (n + 1) x) =
      ∑ i : Fin (n + 1),
        ((-1 : L) ^ (n + i.val) * Matrix.det (fun a b : Fin n => φ a (x (i.succAbove b)))) • x i

/-- The file's support dimension is the library's `exteriorSupportDim`. -/
theorem sdim_eq_exteriorSupportDim {k : ℕ} (ω : ⋀[L]^k V) :
    sdim ω = AlternatingAnalytic.exteriorSupportDim ω := by
  obtain ⟨W, hW, hω, hd⟩ := AlternatingAnalytic.exteriorSupportDim_attained ω
  apply le_antisymm
  · exact Nat.sInf_le ⟨W, hW, hω, hd⟩
  · refine le_csInf ⟨Module.finrank L W, W, hW, hω, rfl⟩ ?_
    rintro n ⟨U, hU, hUω, rfl⟩
    have := hU
    exact AlternatingAnalytic.exteriorSupportDim_le_finrank U hUω

/-- Any map with the contraction formula is the library's last-slot contraction. -/
theorem isContraction_eq {n : ℕ} {φ : Fin n → Module.Dual L V}
    {c : (⋀[L]^(n + 1) V) →ₗ[L] V} (hc : IsContraction φ c) :
    c = AlternatingAnalytic.exteriorLastContraction φ := by
  apply exteriorPower.linearMap_ext
  ext x
  simp only [LinearMap.compAlternatingMap_apply, hc x,
    AlternatingAnalytic.exteriorLastContraction_ιMulti]

/-- **Lemma B.4, part 1.** The contraction `c_φ` exists. -/
theorem part1_contraction_exists
    (L : Type*) [Field L] (V : Type*) [AddCommGroup V] [Module L V] (n : ℕ) (hn : 1 ≤ n)
    (φ : Fin n → Module.Dual L V) :
    ∃ c : (⋀[L]^(n + 1) V) →ₗ[L] V, IsContraction φ c := by
  exact ⟨AlternatingAnalytic.exteriorLastContraction φ,
    AlternatingAnalytic.exteriorLastContraction_ιMulti φ⟩

/-- **Lemma B.4, part 2.** `c_φ(Λ^k W) ⊆ W` for every subspace `W`. -/
theorem part2_contraction_mem
    (L : Type*) [Field L] (V : Type*) [AddCommGroup V] [Module L V] (n : ℕ) (hn : 1 ≤ n)
    (φ : Fin n → Module.Dual L V) (c : (⋀[L]^(n + 1) V) →ₗ[L] V) (hc : IsContraction φ c)
    (W : Submodule L V) (ω : ⋀[L]^(n + 1) V) (hω : ω ∈ supportedBy (n + 1) W) :
    c ω ∈ W := by
  rw [isContraction_eq hc]
  exact AlternatingAnalytic.exteriorLastContraction_mem_support φ W hω

/-- **Lemma B.4, part 3.** `sdim ω ≥ dim span {c_φ(ω) : φ ∈ (V*)^{k-1}}`; in particular the
span is finite-dimensional, which is stated explicitly because `Module.finrank` is `0` on an
infinite-dimensional space. -/
theorem part3_finrank_span_le_sdim
    (L : Type*) [Field L] (V : Type*) [AddCommGroup V] [Module L V] (n : ℕ) (hn : 1 ≤ n)
    (c : (Fin n → Module.Dual L V) → ((⋀[L]^(n + 1) V) →ₗ[L] V))
    (hc : ∀ φ, IsContraction φ (c φ)) (ω : ⋀[L]^(n + 1) V) :
    FiniteDimensional L (Submodule.span L (Set.range fun φ => c φ ω)) ∧
      Module.finrank L (Submodule.span L (Set.range fun φ => c φ ω)) ≤ sdim ω := by
  have hfun : (fun φ => c φ ω) = fun φ => AlternatingAnalytic.exteriorLastContraction φ ω := by
    funext φ
    rw [isContraction_eq (hc φ)]
  rw [hfun, sdim_eq_exteriorSupportDim]
  exact ⟨AlternatingAnalytic.exteriorContractionSpan_finite ω,
    AlternatingAnalytic.exteriorContractionSpan_finrank_le ω⟩

end AlternatingAnalyticChallenge.LemB_4
