import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import AlternatingAnalytic.Algebra.ExteriorFlattening

/-!
# Proof of Lemma B.3

Uses `exteriorFlattening_rank_le` (AlternatingAnalytic/Algebra/ExteriorFlattening.lean) and
`exteriorSupportDim_attained` (AlternatingAnalytic/Algebra/ExteriorSupportDimension.lean).
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
