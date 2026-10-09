import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import AlternatingAnalytic.Algebra.CanonicalExteriorSupport

/-!
# Proof of Proposition B.5

Uses `mem_exteriorPowerSubmodule_iff_contractionSpan_le` and
`exteriorSupportDim_eq_finrank_contractionSpan`
(AlternatingAnalytic/Algebra/CanonicalExteriorSupport.lean).
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

/-- `ω ∈ Λ^k S(ω)`. -/
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

/-- `S(ω)` is the smallest subspace supporting `ω`. -/
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

/-- `S(ω)` is finite-dimensional and `sdim ω = dim S(ω)`. -/
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
