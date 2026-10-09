import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import AlternatingAnalytic.Algebra.DeterminantArray

/-!
# Proof of Lemma B.2

Uses `determinantArraySubmodule` and `determinantArraySubmodule_injective`
(AlternatingAnalytic/Algebra/DeterminantArray.lean).
-/

namespace AlternatingAnalyticChallenge.LemB_2

/-- The determinant array is well defined: some linear map `Λ^k V → L^(S^k)` is given on
pure wedges by the determinant formula. -/
theorem part0_determinantArray_exists
    (L : Type*) [Field L] (S : Type*) (V : Submodule L (S → L)) (k : ℕ) (hk : 1 ≤ k) :
    ∃ Ω : (⋀[L]^k V) →ₗ[L] ((Fin k → S) → L),
      ∀ (y : Fin k → V) (c : Fin k → S),
      Ω (exteriorPower.ιMulti L k y) c = Matrix.det (fun a b => (y b : S → L) (c a)) := by
  exact ⟨AlternatingAnalytic.determinantArraySubmodule V,
    AlternatingAnalytic.determinantArraySubmodule_ιMulti V⟩

/-- The determinant array is injective. -/
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
