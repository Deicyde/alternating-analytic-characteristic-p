import AlternatingAnalytic.Analysis.LaurentTruncation
import AlternatingAnalytic.Analysis.LaurentEvaluation

/-!
# The Laurent expansion converges

Every `x : LaurentField κ r` is the sum over `ℤ` of its monomials `coeff i x • X^i`. Applying
a continuous ring homomorphism `g` gives `g x = ∑ f (coeff i x) t^i` with `f = g ∘ algebraMap`
and `t = g X`. This is the evaluation formula of Lemma D.2(3).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped NNReal Topology

namespace AlternatingAnalytic

variable (κ : Type*) [Field κ] (r : ℝ≥0)

/-- The monomial `c X^n` as an element of the radius-`r` Laurent field. -/
def laurentSingle (n : ℤ) (c : κ) : LaurentField κ r := HahnSeries.single n c

theorem laurentSingle_eq (n : ℤ) (c : κ) :
    laurentSingle κ r n c =
      algebraMap κ (LaurentField κ r) c * polynomialToLaurentField κ r Polynomial.X ^ n := by
  rw [polynomialToLaurentField_X]
  change (HahnSeries.single n c : LaurentSeries κ) =
    algebraMap κ (LaurentSeries κ) c * (HahnSeries.single 1 1 : LaurentSeries κ) ^ n
  rw [← RatFunc.single_zpow, LaurentSeries.algebraMap_apply, HahnSeries.C_apply,
    HahnSeries.single_mul_single, zero_add, mul_one]

theorem coeff_laurentSingle (n i : ℤ) (c : κ) :
    LaurentField.coeff κ r i (laurentSingle κ r n c) = if i = n then c else 0 := by
  rw [LaurentField.coeff_apply, laurentSingle, HahnSeries.coeff_single]
  congr

variable [Fact (0 < r)] [Fact (r < 1)]

/-- A Laurent series is the sum of its monomials. -/
theorem hasSum_laurentSingle (x : LaurentField κ r) :
    HasSum (fun i : ℤ => laurentSingle κ r i (LaurentField.coeff κ r i x)) x := by
  have hr0 : (0 : ℝ) < r := show 0 < r from Fact.out
  have hr1 : (r : ℝ) < 1 := show r < 1 from Fact.out
  rw [HasSum, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε hr1
  set m : ℤ := (show LaurentSeries κ from x).order
  filter_upwards [Filter.eventually_ge_atTop (Finset.Icc m (N : ℤ))] with s hs
  rw [dist_eq_norm]
  refine lt_of_le_of_lt ?_ hN
  have hle : ‖∑ i ∈ s, laurentSingle κ r i (LaurentField.coeff κ r i x) - x‖ ≤
      (r : ℝ) ^ ((N : ℤ) + 1) := by
    apply laurentField_norm_le_of_coeff_eq_zero
    intro n hn
    rw [map_sub, map_sum]
    simp only [coeff_laurentSingle, Finset.sum_ite_eq]
    by_cases hns : n ∈ s
    · simp [hns]
    · have hnm : n < m := by
        by_contra h
        exact hns (hs (Finset.mem_Icc.mpr ⟨not_lt.mp h, by omega⟩))
      simp only [hns, ite_false, zero_sub, neg_eq_zero]
      exact HahnSeries.coeff_eq_zero_of_lt_order hnm
  refine hle.trans ?_
  rw [zpow_add_one₀ hr0.ne', zpow_natCast]
  exact (mul_le_of_le_one_right (pow_nonneg hr0.le N) hr1.le)

/-- A continuous ring homomorphism out of `κ((X))` evaluates each series termwise at the image of `X`. -/
theorem hasSum_eval_of_continuous {K : Type*} [NormedField K] (g : LaurentField κ r →+* K)
    (hg : Continuous g) (f : κ →+* K) (t : K)
    (hf : ∀ c : κ, g (algebraMap κ (LaurentField κ r) c) = f c)
    (ht : g (polynomialToLaurentField κ r Polynomial.X) = t) (x : LaurentField κ r) :
    HasSum (fun i : ℤ => f (LaurentField.coeff κ r i x) * t ^ i) (g x) := by
  have h := (hasSum_laurentSingle κ r x).map g.toAddMonoidHom hg
  convert h using 1
  swap
  · rfl
  funext i
  simp only [Function.comp_apply, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe,
    laurentSingle_eq, map_mul, map_zpow₀, hf, ht]

end AlternatingAnalytic
