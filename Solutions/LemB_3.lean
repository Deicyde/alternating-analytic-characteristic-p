import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import AlternatingAnalytic.Algebra.ExteriorFlattening

/-!
# Lemma B.3 (support bounds flattening rank), p. 27

Setting (Section B.1): `L` a field, `k ≥ 1`, `S` a set, `V ⊆ L^S`, and `Ω : Λ^k V → L^(S^k)`
the determinant array, `Ω_{y₁ ∧ ⋯ ∧ y_k}(c) = det (y_b(c_a))_{a,b}`.

Paper statement: "Let V ⊆ L^S, ω ∈ Λ^k V and α ∈ {1, …, k}. Let R ⊆ S and
R′ ⊆ S^({1,…,k}∖{α}) be finite. The R × R′ matrix M with entries M(c_α, c′) := Ω_ω(c),
where c has c_α in slot α and the entries of c′ in the other slots, has rank at most
sdim(ω)."

Formalization notes:
* `V` is a `Submodule L (S → L)`; slots are `Fin k` (so `α : Fin k` is 0-indexed);
  `S^({1,…,k}∖{α})` is `{i : Fin k // i ≠ α} → S`; `R`, `R′` are `Finset`s and the matrix is
  indexed by their elements.
* As in `LemB_2`, the determinant array is any linear map `Ω` satisfying the determinant
  formula on pure wedges (such a map exists by `LemB_2.part0_determinantArray_exists` and is
  unique).
* `sdim ω` is computed inside `V`, as in the paper.
* `supportedBy k W` (the image of `Λ^k W → Λ^k V`) and `sdim` (Definition B.1, as an
  `sInf` over dimensions of finite-dimensional supporting subspaces) are defined in this
  file in Mathlib terms. `sInf ∅ = 0` cannot occur, since every exterior vector has a
  finite-dimensional supporting subspace.
* The standing assumption `k ≥ 1` of Section B.1 is kept as a hypothesis; the library proof
  does not need it.
-/

namespace AlternatingAnalyticChallenge.LemB_3

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

/-- **Lemma B.3.** The flattening of `Ω ω` along slot `α`, restricted to finite row and
column sets, has rank at most `sdim ω`. -/
theorem flattening_rank_le_sdim
    (L : Type*) [Field L] (S : Type*) (V : Submodule L (S → L)) (k : ℕ) (hk : 1 ≤ k)
    (Ω : (⋀[L]^k V) →ₗ[L] ((Fin k → S) → L))
    (hΩ : ∀ (y : Fin k → V) (c : Fin k → S),
      Ω (exteriorPower.ιMulti L k y) c = Matrix.det (fun a b => (y b : S → L) (c a)))
    (ω : ⋀[L]^k V) (α : Fin k) (R : Finset S) (R' : Finset ({i : Fin k // i ≠ α} → S)) :
    (Matrix.of fun (r : R) (c' : R') =>
        Ω ω (fun i => if h : i = α then (r : S) else (c' : {i : Fin k // i ≠ α} → S) ⟨i, h⟩)).rank
      ≤ sdim ω := by
  have hEq : Ω = AlternatingAnalytic.determinantArraySubmodule V := by
    apply exteriorPower.linearMap_ext
    ext y c
    simp only [LinearMap.compAlternatingMap_apply, hΩ,
      AlternatingAnalytic.determinantArraySubmodule_ιMulti]
  subst hEq
  rw [sdim_eq_exteriorSupportDim]
  exact AlternatingAnalytic.exteriorFlattening_rank_le V ω α (fun r : R => (r : S))
    (fun c' : R' => (c' : {i : Fin k // i ≠ α} → S))

end AlternatingAnalyticChallenge.LemB_3
