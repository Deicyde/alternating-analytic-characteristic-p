import AlternatingAnalytic.Analysis.LaurentField
import AlternatingAnalytic.Analysis.DiscreteSupNorm

/-!
# Bounded Laurent arrays and their coefficients

Bounded arrays `S →ᵇ κ((X))`, the coordinatewise coefficient maps `coeff_n`, and the
embedding of `κ`-valued arrays as constant arrays. Arrays of norm less than one have zero
constant coefficient (Appendix C, Setting).
-/

noncomputable section

open scoped NNReal BoundedContinuousFunction

namespace AlternatingAnalytic

variable (κ : Type*) [Field κ] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)]
variable {S : Type*} [TopologicalSpace S]

/-- The bounded Laurent array space is complete. -/
theorem boundedLaurent_completeSpace : CompleteSpace (S →ᵇ LaurentField κ r) := inferInstance

/-- The bounded Laurent array space has the ultrametric supremum norm. -/
theorem boundedLaurent_isUltrametricDist : IsUltrametricDist (S →ᵇ LaurentField κ r) := by
  constructor
  intro f g h
  apply (BoundedContinuousFunction.dist_le (by positivity)).2
  intro s
  exact (IsUltrametricDist.dist_triangle_max (f s) (g s) (h s)).trans
    (max_le_max (BoundedContinuousFunction.dist_coe_le_dist s)
      (BoundedContinuousFunction.dist_coe_le_dist s))

/-- A Laurent coefficient taken coordinatewise on a bounded array. -/
def boundedLaurentCoeff (n : ℤ) (f : S →ᵇ LaurentField κ r) : S → κ :=
  fun s => LaurentField.coeff κ r n (f s)

@[simp]
theorem boundedLaurentCoeff_add (n : ℤ) (f g : S →ᵇ LaurentField κ r) :
    boundedLaurentCoeff κ r n (f + g) =
      boundedLaurentCoeff κ r n f + boundedLaurentCoeff κ r n g := by
  ext s
  exact (LaurentField.coeff κ r n).map_add (f s) (g s)

@[simp]
theorem boundedLaurentCoeff_sub (n : ℤ) (f g : S →ᵇ LaurentField κ r) :
    boundedLaurentCoeff κ r n (f - g) =
      boundedLaurentCoeff κ r n f - boundedLaurentCoeff κ r n g := by
  ext s
  exact (LaurentField.coeff κ r n).map_sub (f s) (g s)

/-- Coefficient extraction is `κ`-linear. -/
theorem boundedLaurentCoeff_smul_const (n : ℤ) (c : κ) (f : S →ᵇ LaurentField κ r) :
    boundedLaurentCoeff κ r n ((algebraMap κ (LaurentField κ r) c) • f) =
      c • boundedLaurentCoeff κ r n f := by
  ext s
  change LaurentField.coeff κ r n ((algebraMap κ (LaurentField κ r) c) • f s) =
    c • LaurentField.coeff κ r n (f s)
  rw [IsScalarTower.algebraMap_smul]
  exact (LaurentField.coeff κ r n).map_smul c (f s)

/-- Arrays of norm less than one have zero constant coefficient. -/
theorem boundedLaurentCoeff_zero_of_norm_lt_one (f : S →ᵇ LaurentField κ r)
    (hf : ‖f‖ < 1) : boundedLaurentCoeff κ r 0 f = 0 := by
  ext s
  exact LaurentField.coeff_zero_of_norm_lt_one κ r (f s)
    ((f.norm_coe_le_norm s).trans_lt hf)

/-- Arrays at distance less than one have the same constant coefficient. -/
theorem boundedLaurentCoeff_eq_of_norm_sub_lt_one (f g : S →ᵇ LaurentField κ r)
    (hfg : ‖f - g‖ < 1) : boundedLaurentCoeff κ r 0 f = boundedLaurentCoeff κ r 0 g := by
  apply sub_eq_zero.mp
  rw [← boundedLaurentCoeff_sub]
  exact boundedLaurentCoeff_zero_of_norm_lt_one κ r _ hfg

/-- A nonzero bounded array has a least coordinate order `ν`, attained, with `‖f‖ = r ^ ν`. -/
theorem exists_boundedLaurent_order (f : S →ᵇ LaurentField κ r) (hf : f ≠ 0) :
    ∃ ν : ℤ, ‖f‖ = (r : ℝ) ^ ν ∧
      (∃ s, f s ≠ 0 ∧ (show LaurentSeries κ from f s).order = ν) ∧
      ∀ n : ℤ, n < ν → boundedLaurentCoeff κ r n f = 0 := by
  have hr0 : 0 < (r : ℝ) := show 0 < r from Fact.out
  have hr1 : (r : ℝ) < 1 := show r < 1 from Fact.out
  have hd (x : LaurentField κ r) (hx : x ≠ 0) :
      ∃ n : ℤ, ‖x‖ = ((r : ℝ)⁻¹) ^ n := by
    refine ⟨-(show LaurentSeries κ from x).order, ?_⟩
    rw [LaurentField.norm_of_ne_zero κ r x hx]
    simp [zpow_neg]
  obtain ⟨s, hs, hnorm⟩ := exists_norm_eq_of_discrete _ ((one_lt_inv₀ hr0).2 hr1) hd f hf
  let ν := (show LaurentSeries κ from f s).order
  have hnorm' : ‖f‖ = (r : ℝ) ^ ν :=
    hnorm.trans (LaurentField.norm_of_ne_zero κ r (f s) hs)
  refine ⟨ν, hnorm', ⟨s, hs, rfl⟩, ?_⟩
  intro n hn
  ext t
  by_cases ht : f t = 0
  · change LaurentField.coeff κ r n (f t) = 0
    rw [ht, map_zero]
  · have hle : (r : ℝ) ^ (show LaurentSeries κ from f t).order ≤ (r : ℝ) ^ ν := by
      rw [← LaurentField.norm_of_ne_zero κ r (f t) ht, ← hnorm']
      exact f.norm_coe_le_norm t
    exact HahnSeries.coeff_eq_zero_of_lt_order
      (hn.trans_le ((zpow_le_zpow_iff_right_of_lt_one₀ hr0 hr1).1 hle))

section Constants

variable [DiscreteTopology S]

/-- A `κ`-valued array, viewed as an array of constant Laurent series. -/
noncomputable def constantLaurentArray (a : S → κ) : S →ᵇ LaurentField κ r :=
  BoundedContinuousFunction.mkOfDiscrete
    (fun s => algebraMap κ (LaurentField κ r) (a s)) 2 (fun s t => by
      calc
        dist (algebraMap κ (LaurentField κ r) (a s))
            (algebraMap κ (LaurentField κ r) (a t))
            ≤ ‖algebraMap κ (LaurentField κ r) (a s)‖ +
              ‖algebraMap κ (LaurentField κ r) (a t)‖ := dist_le_norm_add_norm _ _
        _ ≤ 2 := by linarith [LaurentField.norm_algebraMap_le_one κ r (a s),
          LaurentField.norm_algebraMap_le_one κ r (a t)])

@[simp]
theorem constantLaurentArray_apply (a : S → κ) (s : S) :
    constantLaurentArray κ r a s = algebraMap κ (LaurentField κ r) (a s) := rfl

theorem constantLaurentArray_injective : Function.Injective (constantLaurentArray κ r (S := S)) := by
  intro a b h
  funext s
  apply (algebraMap κ (LaurentField κ r)).injective
  exact congrArg (fun f : S →ᵇ LaurentField κ r => f s) h

theorem norm_constantLaurentArray_le_one (a : S → κ) : ‖constantLaurentArray κ r a‖ ≤ 1 :=
  (BoundedContinuousFunction.norm_le zero_le_one).2
    (fun s => LaurentField.norm_algebraMap_le_one κ r (a s))

theorem norm_constantLaurentArray (a : S → κ) (ha : a ≠ 0) :
    ‖constantLaurentArray κ r a‖ = 1 := by
  have hne : ∃ s, a s ≠ 0 := by
    by_contra h
    push Not at h
    exact ha (funext h)
  obtain ⟨s, hs⟩ := hne
  apply le_antisymm (norm_constantLaurentArray_le_one κ r a)
  simpa [constantLaurentArray_apply, LaurentField.norm_algebraMap κ r (a s) hs] using
    (constantLaurentArray κ r a).norm_coe_le_norm s

/-- The constant coefficient of a constant array is the array itself. -/
theorem boundedLaurentCoeff_constantLaurentArray (a : S → κ) :
    boundedLaurentCoeff κ r 0 (constantLaurentArray κ r a) = a := by
  ext s
  change (algebraMap κ (LaurentSeries κ) (a s)).coeff 0 = a s
  rw [LaurentSeries.algebraMap_apply, HahnSeries.C_apply, HahnSeries.coeff_single_same]

end Constants

end AlternatingAnalytic
