import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import AlternatingAnalytic.Algebra.DeterminantArray

/-!
# Lemma B.2 (the determinant array is injective), p. 26

Setting (Section B.1, p. 26): `L` is a field, `k ≥ 1`, `S` is a set and `V ⊆ L^S` is a
space of functions on `S`. The determinant array is the linear map
`Ω : Λ^k V → L^(S^k)`, `Ω_{y₁ ∧ ⋯ ∧ y_k}(c₁, …, c_k) := det (y_b(c_a))_{a,b=1}^k`.

Paper statement: "The determinant array Ω : Λ^k V → L^(S^k) is injective."

Formalization notes:
* `V` is a `Submodule L (S → L)`; `Λ^k V` is Mathlib's `⋀[L]^k V`; `S^k` is `Fin k → S`.
* The determinant array is not given by a new definition: both theorems quantify over
  linear maps `Ω` satisfying the defining determinant formula on pure wedges
  `exteriorPower.ιMulti L k y`, with rows indexed by evaluation points `a` and columns by
  vectors `b`, as in the paper. `part0` records that such a map exists (the paper's
  "it is well defined"), so `part1` is not vacuous; such a map is unique since pure wedges
  span `Λ^k V`.
* The standing assumption `k ≥ 1` of Section B.1 is kept as a hypothesis; the library proof
  does not need it.
* No definitions are introduced.
-/

namespace AlternatingAnalyticChallenge.LemB_2

/-- **Definition of the determinant array (p. 26), well-definedness.** There is a linear
map `Λ^k V → L^(S^k)` given on pure wedges by the determinant formula. -/
theorem part0_determinantArray_exists
    (L : Type*) [Field L] (S : Type*) (V : Submodule L (S → L)) (k : ℕ) (hk : 1 ≤ k) :
    ∃ Ω : (⋀[L]^k V) →ₗ[L] ((Fin k → S) → L),
      ∀ (y : Fin k → V) (c : Fin k → S),
      Ω (exteriorPower.ιMulti L k y) c = Matrix.det (fun a b => (y b : S → L) (c a)) := by
  exact ⟨AlternatingAnalytic.determinantArraySubmodule V,
    AlternatingAnalytic.determinantArraySubmodule_ιMulti V⟩

/-- **Lemma B.2.** The determinant array is injective. -/
theorem part1_determinantArray_injective
    (L : Type*) [Field L] (S : Type*) (V : Submodule L (S → L)) (k : ℕ) (hk : 1 ≤ k)
    (Ω : (⋀[L]^k V) →ₗ[L] ((Fin k → S) → L))
    (hΩ : ∀ (y : Fin k → V) (c : Fin k → S),
      Ω (exteriorPower.ιMulti L k y) c = Matrix.det (fun a b => (y b : S → L) (c a))) :
    Function.Injective Ω := by
  have hEq : Ω = AlternatingAnalytic.determinantArraySubmodule V := by
    apply exteriorPower.linearMap_ext
    ext y c
    simp only [LinearMap.compAlternatingMap_apply, hΩ,
      AlternatingAnalytic.determinantArraySubmodule_ιMulti]
  rw [hEq]
  exact AlternatingAnalytic.determinantArraySubmodule_injective V

end AlternatingAnalyticChallenge.LemB_2
