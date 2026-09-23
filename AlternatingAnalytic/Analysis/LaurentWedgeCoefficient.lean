import AlternatingAnalytic.Analysis.LaurentTruncation
import AlternatingAnalytic.Analysis.LaurentMultilinearStability
import AlternatingAnalytic.Analysis.ProjectiveExterior
import AlternatingAnalytic.Algebra.ExteriorSupportDimension
import AlternatingAnalytic.Analysis.GeometricWeightBound

/-! Finite Laurent truncations and the constant coefficient of a pure exterior wedge. -/

noncomputable section

open Module
open scoped NNReal BoundedContinuousFunction

namespace AlternatingAnalytic

variable (κ : Type*) [Field κ] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)]
variable {S : Type*} [TopologicalSpace S] [DiscreteTopology S]

/-- Coordinatewise Laurent coefficient extraction as an additive map. -/
def boundedLaurentCoeffAddHom (n : ℤ) : (S →ᵇ LaurentField κ r) →+ (S → κ) where
  toFun := boundedLaurentCoeff κ r n
  map_zero' := by
    ext s
    exact (LaurentField.coeff κ r n).map_zero
  map_add' := boundedLaurentCoeff_add κ r n

/-- The Laurent monomial with coefficient one, on the normed radius carrier. -/
def laurentMonomial (n : ℤ) : LaurentField κ r := HahnSeries.single n 1

theorem norm_laurentMonomial (n : ℤ) :
    ‖laurentMonomial κ r n‖ = (r : ℝ) ^ n :=
  laurent_norm_single_one κ (r := r) Fact.out Fact.out n

/-- A monomial times a constant array has precisely its prescribed Laurent coefficient. -/
theorem boundedLaurentCoeff_monomial_smul_constant (n m : ℤ) (a : S → κ) :
    boundedLaurentCoeff κ r n (laurentMonomial κ r m • constantLaurentArray κ r a) =
      if n = m then a else 0 := by
  ext s
  change (HahnSeries.single m (1 : κ) * algebraMap κ (LaurentSeries κ) (a s)).coeff n = _
  rw [LaurentSeries.algebraMap_apply, HahnSeries.C_apply, HahnSeries.single_mul_single]
  simp only [add_zero, one_mul, HahnSeries.coeff_single]
  split_ifs <;> rfl

/-- Truncate a bounded Laurent array to the `l + 1` consecutive degrees starting at `ν`. -/
def finiteLaurentTruncation (ν : ℤ) (l : ℕ) (f : S →ᵇ LaurentField κ r) :
    S →ᵇ LaurentField κ r :=
  ∑ j : Fin (l + 1), laurentMonomial κ r (ν + j.val) •
    constantLaurentArray κ r (boundedLaurentCoeff κ r (ν + j.val) f)

theorem boundedLaurentCoeff_finiteLaurentTruncation (ν n : ℤ) (l : ℕ)
    (f : S →ᵇ LaurentField κ r) :
    boundedLaurentCoeff κ r n (finiteLaurentTruncation κ r ν l f) =
      ∑ j : Fin (l + 1), if n = ν + j.val then boundedLaurentCoeff κ r (ν + j.val) f
        else 0 := by
  change boundedLaurentCoeffAddHom κ r n (∑ j : Fin (l + 1), _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact boundedLaurentCoeff_monomial_smul_constant κ r n (ν + j.val) _

theorem finiteLaurentTruncation_coeff_below (ν n : ℤ) (l : ℕ)
    (f : S →ᵇ LaurentField κ r) (hn : n < ν) :
    boundedLaurentCoeff κ r n (finiteLaurentTruncation κ r ν l f) = 0 := by
  rw [boundedLaurentCoeff_finiteLaurentTruncation]
  apply Finset.sum_eq_zero
  intro j _
  rw [ite_eq_right (by omega)]

theorem finiteLaurentTruncation_coeff_within (ν n : ℤ) (l : ℕ)
    (f : S →ᵇ LaurentField κ r) (hν : ν ≤ n) (hn : n < ν + l + 1) :
    boundedLaurentCoeff κ r n (finiteLaurentTruncation κ r ν l f) =
      boundedLaurentCoeff κ r n f := by
  classical
  let j : Fin (l + 1) := ⟨(n - ν).toNat, by omega⟩
  have hj : n = ν + j.val := by dsimp [j]; omega
  rw [boundedLaurentCoeff_finiteLaurentTruncation, Finset.sum_eq_single j]
  · rw [ite_eq_left hj, ← hj]
  · intro i _ hij
    rw [ite_eq_right]
    intro hi
    apply hij
    apply Fin.ext
    omega
  · simp

/-- The finite truncation has no larger norm than its lowest retained monomial. -/
theorem norm_finiteLaurentTruncation_le (ν : ℤ) (l : ℕ)
    (f : S →ᵇ LaurentField κ r) :
    ‖finiteLaurentTruncation κ r ν l f‖ ≤ (r : ℝ) ^ ν :=
  boundedLaurent_norm_le_of_coeff_eq_zero κ r _ ν
    (fun n hn ↦ finiteLaurentTruncation_coeff_below κ r ν n l f hn)

/-- Truncation leaves a remainder with all coefficients through degree `ν + l` zero. -/
theorem norm_sub_finiteLaurentTruncation_le (ν : ℤ) (l : ℕ)
    (f : S →ᵇ LaurentField κ r)
    (hf : ∀ n : ℤ, n < ν → boundedLaurentCoeff κ r n f = 0) :
    ‖f - finiteLaurentTruncation κ r ν l f‖ ≤ (r : ℝ) ^ (ν + l + 1) := by
  apply boundedLaurent_norm_le_of_coeff_eq_zero
  intro n hn
  rw [boundedLaurentCoeff_sub]
  apply sub_eq_zero.mpr
  by_cases hnν : n < ν
  · rw [hf n hnν, finiteLaurentTruncation_coeff_below κ r ν n l f hnν]
  · exact (finiteLaurentTruncation_coeff_within κ r ν n l f (le_of_not_gt hnν) hn).symm

omit [Fact (0 < r)] [Fact (r < 1)] in
/-- Products of monomials add their exponents. -/
theorem prod_laurentMonomial {ι : Type*} (t : Finset ι) (n : ι → ℤ) :
    ∏ i ∈ t, laurentMonomial κ r (n i) = laurentMonomial κ r (∑ i ∈ t, n i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty]
    exact (HahnSeries.single_zero_one (Γ := ℤ) (R := κ)).symm
  | @insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih]
    have h : (HahnSeries.single (n a) (1 : κ) *
        HahnSeries.single (∑ i ∈ t, n i) 1 : LaurentSeries κ) =
        HahnSeries.single (n a + ∑ i ∈ t, n i) 1 := by
      rw [HahnSeries.single_mul_single, one_mul]
    exact h

/-- The actual bounded determinant array, regarded as a continuous alternating map. -/
def laurentDeterminantForm (k : ℕ) :=
  (projectiveExteriorArray (LaurentField κ r) S k).compContinuousAlternatingMap
    (projectiveExteriorWedge (LaurentField κ r) S k)

theorem laurentDeterminantForm_apply (k : ℕ) (x : Fin k → (S →ᵇ LaurentField κ r))
    (c : Fin k → S) :
    laurentDeterminantForm κ r k x c = Matrix.det (fun i j ↦ x j (c i)) :=
  projectiveExteriorArray_wedge (LaurentField κ r) S k x c

theorem laurentDeterminantForm_norm_le (k : ℕ) :
    ‖laurentDeterminantForm κ r (S := S) k‖ ≤ 1 := by
  calc
    _ ≤ ‖projectiveExteriorArray (LaurentField κ r) S k‖ *
        ‖projectiveExteriorWedge (LaurentField κ r) S k‖ :=
      ContinuousLinearMap.norm_compContinuousAlternatingMap_le _ _
    _ ≤ 1 * 1 := mul_le_mul (projectiveExteriorArray_norm_le _ _ _)
      (projectiveExteriorWedge_norm_le _ _ _) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem norm_laurentDeterminantForm_le (k : ℕ) (x : Fin k → (S →ᵇ LaurentField κ r)) :
    ‖laurentDeterminantForm κ r k x‖ ≤ ∏ i, ‖x i‖ := by
  calc
    _ ≤ ‖laurentDeterminantForm κ r k‖ * ∏ i, ‖x i‖ :=
      ContinuousAlternatingMap.le_opNorm _ _
    _ ≤ 1 * ∏ i, ‖x i‖ := mul_le_mul_of_nonneg_right
      (laurentDeterminantForm_norm_le κ r k) (Finset.prod_nonneg fun i _ ↦ norm_nonneg (x i))
    _ = _ := one_mul _

/-- Determinants of constant arrays are obtained by the coefficient-field embedding. -/
theorem laurentDeterminantForm_constant (k : ℕ) (y : Fin k → (S → κ)) :
    laurentDeterminantForm κ r k (fun i ↦ constantLaurentArray κ r (y i)) =
      constantLaurentArray κ r (determinantArray (exteriorPower.ιMulti κ k y)) := by
  ext c
  rw [laurentDeterminantForm_apply, constantLaurentArray_apply, determinantArray_ιMulti]
  calc
    Matrix.det (fun i j ↦ constantLaurentArray κ r (y j) (c i)) =
        Matrix.det ((algebraMap κ (LaurentField κ r)).mapMatrix
          (Matrix.of (fun i j ↦ y j (c i)))) := by
      apply congrArg Matrix.det
      ext i j
      rfl
    _ = _ := ((algebraMap κ (LaurentField κ r)).map_det _).symm

/-- The finite exterior witness obtained by retaining just total exponent zero. -/
def finiteLaurentWedgeCoefficient (k l : ℕ) (ν : Fin k → ℤ)
    (x : Fin k → (S →ᵇ LaurentField κ r)) : ⋀[κ]^k (S → κ) := by
  classical
  exact ∑ n ∈ Finset.univ.filter (fun n : Fin k → Fin (l + 1) ↦
      (∑ i : Fin k, (ν i + (n i).val)) = 0),
    exteriorPower.ιMulti κ k (fun i ↦ boundedLaurentCoeff κ r (ν i + (n i).val) (x i))

omit [DiscreteTopology S] in
/-- Every factor of the finite exterior witness belongs to the span of `k(l + 1)` coefficients. -/
theorem finiteLaurentWedgeCoefficient_support_le (k l : ℕ) (ν : Fin k → ℤ)
    (x : Fin k → (S →ᵇ LaurentField κ r)) :
    exteriorSupportDim (finiteLaurentWedgeCoefficient κ r k l ν x) ≤ k * (l + 1) := by
  classical
  let v : Fin k × Fin (l + 1) → (S → κ) :=
    fun p ↦ boundedLaurentCoeff κ r (ν p.1 + p.2.val) (x p.1)
  let W := Submodule.span κ (Set.range v)
  let : Module.Finite κ W := FiniteDimensional.span_of_finite κ (Set.finite_range v)
  have hmem : finiteLaurentWedgeCoefficient κ r k l ν x ∈ exteriorPowerSubmodule k W := by
    apply Submodule.sum_mem
    intro n hn
    apply ιMulti_mem_exteriorPowerSubmodule
    intro i
    exact Submodule.subset_span ⟨(i, n i), rfl⟩
  exact (exteriorSupportDim_le_finrank W hmem).trans
    (by simpa only [W, Set.finrank, Fintype.card_prod, Fintype.card_fin] using
      (finrank_range_le_card (R := κ) v))

set_option backward.isDefEq.respectTransparency false in
/-- Expanding the finite truncations recovers exactly the determinant array of the finite witness. -/
theorem finiteLaurentWedgeCoefficient_array (k l : ℕ) (ν : Fin k → ℤ)
    (x : Fin k → (S →ᵇ LaurentField κ r)) :
    determinantArray (finiteLaurentWedgeCoefficient κ r k l ν x) =
      boundedLaurentCoeff κ r 0
        (laurentDeterminantForm κ r k (fun i ↦ finiteLaurentTruncation κ r (ν i) l (x i))) := by
  classical
  symm
  calc
    _ = ∑ n : Fin k → Fin (l + 1), boundedLaurentCoeff κ r 0
        (laurentDeterminantForm κ r k (fun i ↦ laurentMonomial κ r (ν i + (n i).val) •
          constantLaurentArray κ r (boundedLaurentCoeff κ r (ν i + (n i).val) (x i)))) := by
      change boundedLaurentCoeffAddHom κ r 0
        (laurentDeterminantForm κ r k (fun i ↦ ∑ j : Fin (l + 1), _)) = _
      rw [ContinuousAlternatingMap.map_sum, map_sum]
      rfl
    _ = ∑ n : Fin k → Fin (l + 1),
        if 0 = (∑ i : Fin k, (ν i + (n i).val)) then
          determinantArray (exteriorPower.ιMulti κ k
            (fun i ↦ boundedLaurentCoeff κ r (ν i + (n i).val) (x i))) else 0 := by
      apply Finset.sum_congr rfl
      intro n _
      calc
        _ = boundedLaurentCoeff κ r 0
            ((∏ i, laurentMonomial κ r (ν i + (n i).val)) •
              laurentDeterminantForm κ r k (fun i ↦ constantLaurentArray κ r
                (boundedLaurentCoeff κ r (ν i + (n i).val) (x i)))) :=
          congrArg (boundedLaurentCoeff κ r 0)
            ((laurentDeterminantForm κ r k).map_smul_univ
              (fun i ↦ laurentMonomial κ r (ν i + (n i).val))
              (fun i ↦ constantLaurentArray κ r
                (boundedLaurentCoeff κ r (ν i + (n i).val) (x i))))
        _ = _ := by rw [prod_laurentMonomial,
          laurentDeterminantForm_constant, boundedLaurentCoeff_monomial_smul_constant]
    _ = _ := by
      simp only [finiteLaurentWedgeCoefficient, map_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n _
      by_cases h : (∑ i : Fin k, (ν i + (n i).val)) = 0
      · rw [ite_eq_left h.symm, ite_eq_left h]
      · rw [ite_eq_right (Ne.symm h), ite_eq_right h, map_zero]

/-- The attained maximum of the geometric weights `(l + 1) r^l`. -/
def geometricWeightMaximum : ℝ :=
  let n := Classical.choose (exists_geometricWeight_max (NNReal.coe_nonneg r)
    (show (r : ℝ) < 1 from (show r < 1 from Fact.out)))
  ((n : ℝ) + 1) * (r : ℝ) ^ n

omit [Fact (0 < r)] in
theorem one_le_geometricWeightMaximum : 1 ≤ geometricWeightMaximum r :=
  (Classical.choose_spec (exists_geometricWeight_max (NNReal.coe_nonneg r)
    (show (r : ℝ) < 1 from (show r < 1 from Fact.out)))).1

omit [Fact (0 < r)] in
theorem geometricWeight_le_maximum (l : ℕ) :
    ((l : ℝ) + 1) * (r : ℝ) ^ l ≤ geometricWeightMaximum r :=
  (Classical.choose_spec (exists_geometricWeight_max (NNReal.coe_nonneg r)
    (show (r : ℝ) < 1 from (show r < 1 from Fact.out)))).2 l

theorem add_one_le_geometricWeightMaximum_mul_zpow (l : ℕ) :
    (l : ℝ) + 1 ≤ geometricWeightMaximum r * (r : ℝ) ^ (-(l : ℤ)) := by
  rw [zpow_neg, zpow_natCast, ← div_eq_mul_inv]
  exact (le_div_iff₀ (pow_pos
    (show 0 < (r : ℝ) from (show 0 < r from Fact.out)) l)).2 (geometricWeight_le_maximum r l)

omit [Fact (r < 1)] in
/-- A finite product of geometric powers equals the power of the sum of the exponents. -/
theorem prod_radius_zpow {ι : Type*} (t : Finset ι) (ν : ι → ℤ) :
    ∏ i ∈ t, (r : ℝ) ^ (ν i) = (r : ℝ) ^ (∑ i ∈ t, ν i) := by
  classical
  have hr : (r : ℝ) ≠ 0 := ne_of_gt (show 0 < (r : ℝ) from (show 0 < r from Fact.out))
  induction t using Finset.induction_on with
  | empty => simp
  | @insert a t ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hr]

omit [DiscreteTopology S] in
/-- The finite support bound has the required geometric normalization when the orders add to `-l`. -/
theorem finiteLaurentWedgeCoefficient_support_norm_le (k l : ℕ) (ν : Fin k → ℤ)
    (x : Fin k → (S →ᵇ LaurentField κ r))
    (hnorm : ∀ i, ‖x i‖ = (r : ℝ) ^ (ν i)) (hsum : (∑ i, ν i) = -(l : ℤ)) :
    (exteriorSupportDim (finiteLaurentWedgeCoefficient κ r k l ν x) : ℝ) ≤
      (k : ℝ) * geometricWeightMaximum r * ∏ i, ‖x i‖ := by
  have hp : (∏ i, ‖x i‖) = (r : ℝ) ^ (-(l : ℤ)) := by
    calc
      _ = ∏ i, (r : ℝ) ^ (ν i) := Finset.prod_congr rfl (fun i _ ↦ hnorm i)
      _ = (r : ℝ) ^ (∑ i, ν i) := prod_radius_zpow r Finset.univ ν
      _ = _ := by rw [hsum]
  calc
    _ ≤ ((k * (l + 1) : ℕ) : ℝ) := by
      exact_mod_cast finiteLaurentWedgeCoefficient_support_le κ r k l ν x
    _ = (k : ℝ) * ((l : ℝ) + 1) := by push_cast; rfl
    _ ≤ (k : ℝ) * (geometricWeightMaximum r * (r : ℝ) ^ (-(l : ℤ))) :=
      mul_le_mul_of_nonneg_left (add_one_le_geometricWeightMaximum_mul_zpow r l)
        (Nat.cast_nonneg k)
    _ = _ := by rw [hp, mul_assoc]

/-- A pure wedge with product norm less than one has zero constant determinant coefficient. -/
theorem exists_laurentWedgeCoefficient_of_small (k : ℕ)
    (x : Fin k → (S →ᵇ LaurentField κ r)) (hsmall : (∏ i, ‖x i‖) < 1) :
    ∃ β : ⋀[κ]^k (S → κ),
      determinantArray β = boundedLaurentCoeff κ r 0 (laurentDeterminantForm κ r k x) ∧
      exteriorSupportDim β = 0 := by
  refine ⟨0, ?_, exteriorSupportDim_zero⟩
  rw [map_zero]
  exact (boundedLaurentCoeff_zero_of_norm_lt_one κ r _
    ((norm_laurentDeterminantForm_le κ r k x).trans_lt hsmall)).symm

set_option backward.isDefEq.respectTransparency false

/-- The finite witness also represents the original determinant, because the omitted tails
have zero constant coefficient in every multilinear difference term. -/
theorem finiteLaurentWedgeCoefficient_represents (k l : ℕ) (ν : Fin k → ℤ)
    (x : Fin k → (S →ᵇ LaurentField κ r))
    (hbelow : ∀ i n, n < ν i → boundedLaurentCoeff κ r n (x i) = 0)
    (hx : ∀ i, ‖x i‖ ≤ (r : ℝ) ^ (ν i)) (hsum : (∑ i, ν i) = -(l : ℤ)) :
    determinantArray (finiteLaurentWedgeCoefficient κ r k l ν x) =
      boundedLaurentCoeff κ r 0 (laurentDeterminantForm κ r k x) := by
  rw [finiteLaurentWedgeCoefficient_array]
  symm
  exact boundedLaurentCoeff_multilinear_stable κ r
    (laurentDeterminantForm κ r k).toMultilinearMap
    (norm_laurentDeterminantForm_le κ r k) ν l hsum x
    (fun i ↦ finiteLaurentTruncation κ r (ν i) l (x i)) hx
    (fun i ↦ norm_finiteLaurentTruncation_le κ r (ν i) l (x i))
    (fun i ↦ norm_sub_finiteLaurentTruncation_le κ r (ν i) l (x i) (hbelow i))

/-- The constant determinant coefficient of every pure Laurent wedge is an actual exterior
vector over the coefficient field, with the required uniform support estimate. -/
theorem exists_laurentWedgeCoefficient (k : ℕ)
    (x : Fin k → (S →ᵇ LaurentField κ r)) :
    ∃ β : ⋀[κ]^k (S → κ),
      determinantArray β = boundedLaurentCoeff κ r 0 (laurentDeterminantForm κ r k x) ∧
      (exteriorSupportDim β : ℝ) ≤
        (k : ℝ) * geometricWeightMaximum r * ∏ i, ‖x i‖ := by
  classical
  by_cases hsmall : (∏ i, ‖x i‖) < 1
  · obtain ⟨β, hβ, hdim⟩ := exists_laurentWedgeCoefficient_of_small κ r k x hsmall
    refine ⟨β, hβ, ?_⟩
    rw [hdim, Nat.cast_zero]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg k)
      (zero_le_one.trans (one_le_geometricWeightMaximum r)))
      (Finset.prod_nonneg fun i _ ↦ norm_nonneg (x i))
  · have hx : ∀ i, x i ≠ 0 := by
      intro i hi
      apply hsmall
      have hp : (∏ j, ‖x j‖) = 0 := Finset.prod_eq_zero (Finset.mem_univ i)
        (by simp only [hi, norm_zero])
      rw [hp]
      exact zero_lt_one
    choose ν hν using fun i : Fin k ↦ exists_boundedLaurent_order κ r (x i) (hx i)
    have hp : (∏ i, ‖x i‖) = (r : ℝ) ^ (∑ i, ν i) := by
      calc
        _ = ∏ i, (r : ℝ) ^ (ν i) := Finset.prod_congr rfl (fun i _ ↦ (hν i).1)
        _ = _ := prod_radius_zpow r Finset.univ ν
    have hsum0 : (∑ i, ν i) ≤ 0 := by
      apply (zpow_le_zpow_iff_right_of_lt_one₀
        (show 0 < (r : ℝ) from (show 0 < r from Fact.out))
        (show (r : ℝ) < 1 from (show r < 1 from Fact.out))).mp
      rw [zpow_zero, ← hp]
      exact le_of_not_gt hsmall
    let l : ℕ := (-(∑ i, ν i)).toNat
    have hsum : (∑ i, ν i) = -(l : ℤ) := by dsimp [l]; omega
    refine ⟨finiteLaurentWedgeCoefficient κ r k l ν x, ?_, ?_⟩
    · exact finiteLaurentWedgeCoefficient_represents κ r k l ν x
        (fun i ↦ (hν i).2.2) (fun i ↦ (hν i).1.le) hsum
    · exact finiteLaurentWedgeCoefficient_support_norm_le κ r k l ν x
        (fun i ↦ (hν i).1) hsum

/-- The single-wedge coefficient witness, its geometric support bound, and its explicit
finite formula when the lower orders add to a nonpositive integer. -/
theorem laurentWedgeCoefficient_properties (k : ℕ) :
    (∀ x : Fin k → (S →ᵇ LaurentField κ r), ∃ β : ⋀[κ]^k (S → κ),
      determinantArray β = boundedLaurentCoeff κ r 0 (laurentDeterminantForm κ r k x) ∧
      (exteriorSupportDim β : ℝ) ≤
        (k : ℝ) * geometricWeightMaximum r * ∏ i, ‖x i‖) ∧
    (∀ (l : ℕ) (ν : Fin k → ℤ) (x : Fin k → (S →ᵇ LaurentField κ r)),
      (∀ i n, n < ν i → boundedLaurentCoeff κ r n (x i) = 0) →
      (∀ i, ‖x i‖ = (r : ℝ) ^ (ν i)) → (∑ i, ν i) = -(l : ℤ) →
      determinantArray (finiteLaurentWedgeCoefficient κ r k l ν x) =
        boundedLaurentCoeff κ r 0 (laurentDeterminantForm κ r k x) ∧
      exteriorSupportDim (finiteLaurentWedgeCoefficient κ r k l ν x) ≤ k * (l + 1)) := by
  refine ⟨exists_laurentWedgeCoefficient κ r k, ?_⟩
  intro l ν x hbelow hnorm hsum
  exact ⟨finiteLaurentWedgeCoefficient_represents κ r k l ν x hbelow
    (fun i ↦ (hnorm i).le) hsum, finiteLaurentWedgeCoefficient_support_le κ r k l ν x⟩

end AlternatingAnalytic
