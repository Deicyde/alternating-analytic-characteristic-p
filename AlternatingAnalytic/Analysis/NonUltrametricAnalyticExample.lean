import Mathlib.Algebra.Field.ZMod
import AlternatingAnalytic.Analysis.LaurentCompletedCoefficient
import AlternatingAnalytic.Analysis.FactorialInvertible
import AlternatingAnalytic.Analysis.LiftCriterion

/-!
# A target without a nonarchimedean norm, with analytic precomposition

The Laurent exterior target `B` of Appendix C has no equivalent nonarchimedean norm when `k ≥ 2`
(Proposition E.1), yet precomposition into it is analytic whenever `k! ≠ 0` (Proposition 4.1). So
the absence of such a norm does not by itself force nonanalyticity.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NNReal BoundedContinuousFunction

namespace AlternatingAnalytic

open Round24Transfer

/-- For `k ≥ 2` with `k! ≠ 0`, the Laurent exterior target has no equivalent nonarchimedean norm
and precomposition into it is analytic everywhere. -/
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

/-- The case `k = 3` over `F_5((X))`. -/
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
