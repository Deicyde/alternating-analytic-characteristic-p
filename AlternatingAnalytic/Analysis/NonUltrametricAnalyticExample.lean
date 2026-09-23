import Mathlib.Algebra.Field.ZMod
import AlternatingAnalytic.Analysis.LaurentCompletedCoefficient
import AlternatingAnalytic.Analysis.FactorialInvertible
import AlternatingAnalytic.Analysis.LiftCriterion

/-! The absence of an equivalent ultrametric norm is not sufficient for nonanalyticity. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NNReal BoundedContinuousFunction

namespace AlternatingAnalytic

open Round24Transfer

/-- The very same Laurent Banach targets with growing unit sums can have analytic
precomposition whenever the degree factorial is nonzero. -/
theorem laurent_analytic_without_equivalentUltrametricNorm
    (κ : Type*) [Field κ] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)]
    (k : ℕ) (hk : 2 ≤ k) (hfact : (k.factorial : LaurentField κ r) ≠ 0) :
    ¬ HasEquivalentUltrametricNorm (LaurentField κ r)
      (ProjectiveExteriorCompletion (LaurentField κ r) ℕ k) ∧
    ∀ f : (ℕ →ᵇ LaurentField κ r) →L[LaurentField κ r] (ℕ →ᵇ LaurentField κ r),
      AnalyticAt (LaurentField κ r)
        (Q (LaurentField κ r) (Fin k) (ℕ →ᵇ LaurentField κ r)
          (ℕ →ᵇ LaurentField κ r) (ProjectiveExteriorCompletion (LaurentField κ r) ℕ k)) f := by
  refine ⟨laurentExterior_not_hasEquivalentUltrametricNorm κ r k hk, fun f => ?_⟩
  exact (ContinuousAlternatingMap.cpolynomialAt_compContinuousLinearMapCLM
    (ι := Fin k) (by simpa using hfact) f).analyticAt

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The paper's explicit degree-three, characteristic-five example. -/
theorem degree_three_char_five_analytic_without_equivalentUltrametricNorm
    (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] :
    ¬ HasEquivalentUltrametricNorm (LaurentField (ZMod 5) r)
      (ProjectiveExteriorCompletion (LaurentField (ZMod 5) r) ℕ 3) ∧
    ∀ f : (ℕ →ᵇ LaurentField (ZMod 5) r) →L[LaurentField (ZMod 5) r]
        (ℕ →ᵇ LaurentField (ZMod 5) r),
      AnalyticAt (LaurentField (ZMod 5) r)
        (Q (LaurentField (ZMod 5) r) (Fin 3) (ℕ →ᵇ LaurentField (ZMod 5) r)
          (ℕ →ᵇ LaurentField (ZMod 5) r)
          (ProjectiveExteriorCompletion (LaurentField (ZMod 5) r) ℕ 3)) f := by
  apply laurent_analytic_without_equivalentUltrametricNorm (ZMod 5) r 3 (by decide)
  rw [Ne, CharP.cast_eq_zero_iff (LaurentField (ZMod 5) r) 5]
  decide

end AlternatingAnalytic
