import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Lemma B.3 (support bounds flattening rank), p. 29

Setting (Section B.1): `L` a field, `k ≥ 1`, `S` a set, `V ⊆ L^S`, and `Ω : Λ^k V → L^(S^k)`
the determinant array, `Ω_{y₁ ∧ ⋯ ∧ y_k}(c) = det (y_b(c_a))_{a,b}`.

Paper statement: "Let V ⊆ L^S, ω ∈ Λ^k V and α ∈ {1, …, k}. Let R ⊆ S and
R′ ⊆ S^({1,…,k}∖{α}) be finite. The R × R′ matrix M with entries M(c_α, c′) := Ω_ω(c),
where c has c_α in slot α and the entries of c′ in the other slots, has rank at most
sdim(ω)."

## Formalization notes
* `V` is a `Submodule L (S → L)`; slots are `Fin k`, so `α` is 0-indexed;
  `S^({1,…,k}∖{α})` is `{i : Fin k // i ≠ α} → S`; `R` and `R′` are `Finset`s.
* As in `LemB_2`, `Ω` is any linear map satisfying the determinant formula on pure wedges.
* `sdim ω` is computed inside `V`.
* `supportedBy k W` (the image of `Λ^k W → Λ^k V`) and `sdim` (Definition B.1) are defined
  here. `sdim` is an `sInf` over a set that is never empty.
* The hypothesis `k ≥ 1` of Section B.1 is kept but not used.
-/

namespace AlternatingAnalyticChallenge.LemB_3

variable {L : Type*} [Field L] {V : Type*} [AddCommGroup V] [Module L V]

/-- The image of `Λ^k W` in `Λ^k V` (Section B.1); `ω` lies in it when `W` supports `ω`. -/
noncomputable def supportedBy (k : ℕ) (W : Submodule L V) : Submodule L (⋀[L]^k V) :=
  LinearMap.range (exteriorPower.map k W.subtype)

/-- The support dimension of Definition B.1:
`sdim ω = min {dim W : W ⊆ V finite-dimensional, ω ∈ Λ^k W}`. -/
noncomputable def sdim {k : ℕ} (ω : ⋀[L]^k V) : ℕ :=
  sInf {n : ℕ | ∃ W : Submodule L V, FiniteDimensional L W ∧ ω ∈ supportedBy k W ∧
    Module.finrank L W = n}

/-- The flattening of `Ω ω` along slot `α`, restricted to finite row and column sets, has
rank at most `sdim ω`. -/
theorem flattening_rank_le_sdim
    (L : Type*) [Field L] (S : Type*) (V : Submodule L (S → L)) (k : ℕ) (hk : 1 ≤ k)
    (Ω : (⋀[L]^k V) →ₗ[L] ((Fin k → S) → L))
    (hΩ : ∀ (y : Fin k → V) (c : Fin k → S),
      Ω (exteriorPower.ιMulti L k y) c = Matrix.det (fun a b => (y b : S → L) (c a)))
    (ω : ⋀[L]^k V) (α : Fin k) (R : Finset S) (R' : Finset ({i : Fin k // i ≠ α} → S)) :
    (Matrix.of fun (r : R) (c' : R') =>
        Ω ω (fun i => if h : i = α then (r : S) else (c' : {i : Fin k // i ≠ α} → S) ⟨i, h⟩)).rank
      ≤ sdim ω := by
  sorry

end AlternatingAnalyticChallenge.LemB_3
