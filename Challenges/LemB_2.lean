import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Lemma B.2 (the determinant array is injective), p. 27

Setting (Section B.1, p. 27): `L` is a field, `k ≥ 1`, `S` is a set and `V ⊆ L^S` is a
space of functions on `S`. The determinant array is the linear map
`Ω : Λ^k V → L^(S^k)`, `Ω_{y₁ ∧ ⋯ ∧ y_k}(c₁, …, c_k) := det (y_b(c_a))_{a,b=1}^k`.

Paper statement: "The determinant array Ω : Λ^k V → L^(S^k) is injective."

## Formalization notes
* `V` is a `Submodule L (S → L)`; `Λ^k V` is `⋀[L]^k V`; `S^k` is `Fin k → S`.
* The determinant array is not defined. The theorems take any linear map `Ω` given on pure
  wedges `exteriorPower.ιMulti L k y` by the determinant formula, with rows indexed by points
  `a` and columns by vectors `b`. Such a map is unique, and `part0` shows that it exists.
* The hypothesis `k ≥ 1` of Section B.1 is kept but not used.
-/

namespace AlternatingAnalyticChallenge.LemB_2

/-- The determinant array is well defined: some linear map `Λ^k V → L^(S^k)` is given on
pure wedges by the determinant formula. -/
theorem part0_determinantArray_exists
    (L : Type*) [Field L] (S : Type*) (V : Submodule L (S → L)) (k : ℕ) (hk : 1 ≤ k) :
    ∃ Ω : (⋀[L]^k V) →ₗ[L] ((Fin k → S) → L),
      ∀ (y : Fin k → V) (c : Fin k → S),
      Ω (exteriorPower.ιMulti L k y) c = Matrix.det (fun a b => (y b : S → L) (c a)) := by
  sorry

/-- The determinant array is injective. -/
theorem part1_determinantArray_injective
    (L : Type*) [Field L] (S : Type*) (V : Submodule L (S → L)) (k : ℕ) (hk : 1 ≤ k)
    (Ω : (⋀[L]^k V) →ₗ[L] ((Fin k → S) → L))
    (hΩ : ∀ (y : Fin k → V) (c : Fin k → S),
      Ω (exteriorPower.ιMulti L k y) c = Matrix.det (fun a b => (y b : S → L) (c a))) :
    Function.Injective Ω := by
  sorry

end AlternatingAnalyticChallenge.LemB_2
