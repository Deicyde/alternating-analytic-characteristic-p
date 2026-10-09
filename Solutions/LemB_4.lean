import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import AlternatingAnalytic.Algebra.ExteriorContraction

/-!
# Proof of Lemma B.4

Uses `exteriorLastContraction`, `exteriorLastContraction_mem_support` and
`exteriorContractionSpan_finrank_le` (AlternatingAnalytic/Algebra/ExteriorContraction.lean).
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

/-- `sdim` agrees with the library's `exteriorSupportDim`. -/
theorem sdim_eq_exteriorSupportDim {k : ℕ} (ω : ⋀[L]^k V) :
    sdim ω = AlternatingAnalytic.exteriorSupportDim ω := by
  obtain ⟨W, hW, hω, hd⟩ := AlternatingAnalytic.exteriorSupportDim_attained ω
  apply le_antisymm
  · exact Nat.sInf_le ⟨W, hW, hω, hd⟩
  · refine le_csInf ⟨Module.finrank L W, W, hW, hω, rfl⟩ ?_
    rintro n ⟨U, hU, hUω, rfl⟩
    have := hU
    exact AlternatingAnalytic.exteriorSupportDim_le_finrank U hUω

/-- A map satisfying the contraction formula equals `exteriorLastContraction φ`. -/
theorem isContraction_eq {n : ℕ} {φ : Fin n → Module.Dual L V}
    {c : (⋀[L]^(n + 1) V) →ₗ[L] V} (hc : IsContraction φ c) :
    c = AlternatingAnalytic.exteriorLastContraction φ := by
  apply exteriorPower.linearMap_ext
  ext x
  simp only [LinearMap.compAlternatingMap_apply, hc x,
    AlternatingAnalytic.exteriorLastContraction_ιMulti]

/-- The contraction `c_φ` exists. -/
theorem part1_contraction_exists
    (L : Type*) [Field L] (V : Type*) [AddCommGroup V] [Module L V] (n : ℕ) (hn : 1 ≤ n)
    (φ : Fin n → Module.Dual L V) :
    ∃ c : (⋀[L]^(n + 1) V) →ₗ[L] V, IsContraction φ c := by
  exact ⟨AlternatingAnalytic.exteriorLastContraction φ,
    AlternatingAnalytic.exteriorLastContraction_ιMulti φ⟩

/-- `c_φ(Λ^k W) ⊆ W` for every subspace `W`. -/
theorem part2_contraction_mem
    (L : Type*) [Field L] (V : Type*) [AddCommGroup V] [Module L V] (n : ℕ) (hn : 1 ≤ n)
    (φ : Fin n → Module.Dual L V) (c : (⋀[L]^(n + 1) V) →ₗ[L] V) (hc : IsContraction φ c)
    (W : Submodule L V) (ω : ⋀[L]^(n + 1) V) (hω : ω ∈ supportedBy (n + 1) W) :
    c ω ∈ W := by
  rw [isContraction_eq hc]
  exact AlternatingAnalytic.exteriorLastContraction_mem_support φ W hω

/-- The span of `{c_φ(ω) : φ ∈ (V*)^{k-1}}` is finite-dimensional, of dimension at most
`sdim ω`. -/
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
