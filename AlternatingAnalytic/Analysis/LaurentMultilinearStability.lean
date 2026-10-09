import AlternatingAnalytic.Analysis.LaurentCoefficients
import Mathlib.Analysis.Normed.Module.Multilinear.Basic

/-!
# Stability of constant coefficients under multilinear maps

If `A` is a multilinear map into bounded Laurent arrays with `‖A z‖ ≤ ∏ ‖z i‖`, and `x`, `y`
agree to high enough order, then `A x` and `A y` have the same constant coefficient, since
their difference has norm less than one. It is used in the proof of the support estimate,
Proposition C.3.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped NNReal BoundedContinuousFunction
open Finset

namespace AlternatingAnalytic

variable (κ : Type*) [Field κ] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)]
variable {E T : Type*} [NormedAddCommGroup E] [NormedSpace (LaurentField κ r) E]
  [TopologicalSpace T] {k : ℕ}

/-- If `‖x i‖, ‖y i‖ ≤ r ^ ν i`, `‖x i - y i‖ ≤ r ^ (ν i + l + 1)` and `∑ ν i = -l`, then
`A x` and `A y` have the same constant coefficient. -/
theorem boundedLaurentCoeff_multilinear_stable
    (A : MultilinearMap (LaurentField κ r) (fun _ : Fin k => E) (T →ᵇ LaurentField κ r))
    (hA : ∀ z, ‖A z‖ ≤ ∏ i, ‖z i‖)
    (ν : Fin k → ℤ) (l : ℕ) (hsum : ∑ i, ν i = -(l : ℤ))
    (x y : Fin k → E)
    (hx : ∀ i, ‖x i‖ ≤ (r : ℝ) ^ ν i)
    (hy : ∀ i, ‖y i‖ ≤ (r : ℝ) ^ ν i)
    (he : ∀ i, ‖x i - y i‖ ≤ (r : ℝ) ^ (ν i + l + 1)) :
    boundedLaurentCoeff κ r 0 (A x) = boundedLaurentCoeff κ r 0 (A y) := by
  classical
  have hr0 : (0 : ℝ) < r := show 0 < r from Fact.out
  have hr1 : (r : ℝ) < 1 := show r < 1 from Fact.out
  let C : (T →ᵇ LaurentField κ r) →+ (T → κ) :=
    { toFun := boundedLaurentCoeff κ r 0
      map_zero' := by ext t; exact (LaurentField.coeff κ r 0).map_zero
      map_add' := boundedLaurentCoeff_add κ r 0 }
  let z (i j : Fin k) := if j < i then x j else if i = j then x j - y j else y j
  have hdiff : A x - A y = ∑ i, A (z i) := by
    simpa only [Finset.piecewise_univ, Finset.mem_univ, true_implies, z] using
      A.map_sub_map_piecewise x y Finset.univ
  have hprod (s : Finset (Fin k)) (a : Fin k → ℤ) :
      (∏ j ∈ s, (r : ℝ) ^ a j) = (r : ℝ) ^ (∑ j ∈ s, a j) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, zpow_add₀ hr0.ne']
  have hterm (i : Fin k) : C (A (z i)) = 0 := by
    apply boundedLaurentCoeff_zero_of_norm_lt_one κ r
    have hz (j : Fin k) :
        ‖z i j‖ ≤ (r : ℝ) ^ (ν j + if j = i then (l : ℤ) + 1 else 0) := by
      by_cases hji : j = i
      · subst j
        simpa only [z, lt_self_iff_false, ite_false, ite_true, add_assoc] using he i
      · by_cases hlt : j < i
        · simpa only [z, hlt, ite_true, hji, ite_false, add_zero] using hx j
        · simpa only [z, hlt, ite_false, hji, Ne.symm hji, add_zero] using hy j
    have hp : (∏ j, (r : ℝ) ^ (ν j + if j = i then (l : ℤ) + 1 else 0)) = r := by
      rw [hprod, Finset.sum_add_distrib, hsum]
      simp
    exact ((hA (z i)).trans
      ((Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) (fun j _ => hz j)).trans_eq hp)).trans_lt hr1
  change C (A x) = C (A y)
  apply sub_eq_zero.mp
  rw [← map_sub, hdiff, map_sum]
  exact Finset.sum_eq_zero (fun i _ => hterm i)

end AlternatingAnalytic
