import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import AlternatingAnalytic.Algebra.CanonicalExteriorSupport

/-!
# Proposition B.5 (canonical exterior support), p. 27

Paper statement: "Let L be any field, V an L-vector space, k ≥ 2, and ω ∈ Λ^k V. Then
S(ω) := span{c_φ(ω) : φ ∈ (V*)^{k−1}}
is the unique smallest subspace supporting ω. In particular, ω ∈ Λ^k S(ω) and
sdim(ω) = dim S(ω)."  Here `c_φ` is the contraction of Lemma B.4.

Formalization notes:
* The degree is written `k = n + 1` with hypothesis `1 ≤ n` (that is, `k ≥ 2`); slots are
  0-indexed (`Fin (n + 1)`), and `V*` is the algebraic dual `Module.Dual L V`.
* `IsContraction φ c` (defined in this file) says that the linear map `c` satisfies the
  displayed formula on pure wedges `exteriorPower.ιMulti`; such a map exists by
  `LemB_4.part1_contraction_exists` and is unique because pure wedges span `Λ^k V`.
* The library proves the proposition for every `n`, including `n = 0`; the hypothesis
  `1 ≤ n` is kept for faithfulness to the paper and is unused.
* `S(ω)` is `Submodule.span L (Set.range fun φ => c φ ω)` for any family `c` of maps with
  the contraction formula.
* "Unique smallest subspace supporting ω" is stated as `part1` (`S(ω)` supports `ω`) and
  `part2` (a subspace `W` supports `ω` iff `S(ω) ≤ W`); uniqueness of a least element is
  automatic. `part3` states that `S(ω)` is finite-dimensional (used implicitly by the
  paper's "dim S(ω)") and `sdim ω = finrank S(ω)`.
* `supportedBy k W` (the image of `Λ^k W → Λ^k V`) and `sdim` (Definition B.1, as an
  `sInf` over dimensions of finite-dimensional supporting subspaces) are defined in this
  file in Mathlib terms. `sInf ∅ = 0` cannot occur, since every exterior vector has a
  finite-dimensional supporting subspace.
* The degree-zero and degree-one remarks after the proposition are not part of this claim.
-/

namespace AlternatingAnalyticChallenge.PropB_5

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

/-- **Proposition B.5, part 1.** `ω ∈ Λ^k S(ω)`. -/
theorem part1_mem_supportedBy_span
    (L : Type*) [Field L] (V : Type*) [AddCommGroup V] [Module L V] (n : ℕ) (hn : 1 ≤ n)
    (c : (Fin n → Module.Dual L V) → ((⋀[L]^(n + 1) V) →ₗ[L] V))
    (hc : ∀ φ, IsContraction φ (c φ)) (ω : ⋀[L]^(n + 1) V) :
    ω ∈ supportedBy (n + 1) (Submodule.span L (Set.range fun φ => c φ ω)) := by
  have hfun : (fun φ => c φ ω) = fun φ => AlternatingAnalytic.exteriorLastContraction φ ω := by
    funext φ
    rw [isContraction_eq (hc φ)]
  rw [hfun]
  exact AlternatingAnalytic.mem_exteriorPowerSubmodule_contractionSpan ω

/-- **Proposition B.5, part 2.** `S(ω)` is the smallest subspace supporting `ω`. -/
theorem part2_supportedBy_iff_span_le
    (L : Type*) [Field L] (V : Type*) [AddCommGroup V] [Module L V] (n : ℕ) (hn : 1 ≤ n)
    (c : (Fin n → Module.Dual L V) → ((⋀[L]^(n + 1) V) →ₗ[L] V))
    (hc : ∀ φ, IsContraction φ (c φ)) (ω : ⋀[L]^(n + 1) V) (W : Submodule L V) :
    ω ∈ supportedBy (n + 1) W ↔ Submodule.span L (Set.range fun φ => c φ ω) ≤ W := by
  have hfun : (fun φ => c φ ω) = fun φ => AlternatingAnalytic.exteriorLastContraction φ ω := by
    funext φ
    rw [isContraction_eq (hc φ)]
  rw [hfun]
  exact AlternatingAnalytic.mem_exteriorPowerSubmodule_iff_contractionSpan_le W ω

/-- **Proposition B.5, part 3.** `S(ω)` is finite-dimensional and `sdim ω = dim S(ω)`. -/
theorem part3_sdim_eq_finrank_span
    (L : Type*) [Field L] (V : Type*) [AddCommGroup V] [Module L V] (n : ℕ) (hn : 1 ≤ n)
    (c : (Fin n → Module.Dual L V) → ((⋀[L]^(n + 1) V) →ₗ[L] V))
    (hc : ∀ φ, IsContraction φ (c φ)) (ω : ⋀[L]^(n + 1) V) :
    FiniteDimensional L (Submodule.span L (Set.range fun φ => c φ ω)) ∧
      sdim ω = Module.finrank L (Submodule.span L (Set.range fun φ => c φ ω)) := by
  have hfun : (fun φ => c φ ω) = fun φ => AlternatingAnalytic.exteriorLastContraction φ ω := by
    funext φ
    rw [isContraction_eq (hc φ)]
  rw [hfun]
  rw [sdim_eq_exteriorSupportDim]
  exact ⟨AlternatingAnalytic.exteriorContractionSpan_finite ω,
    AlternatingAnalytic.exteriorSupportDim_eq_finrank_contractionSpan ω⟩

end AlternatingAnalyticChallenge.PropB_5
