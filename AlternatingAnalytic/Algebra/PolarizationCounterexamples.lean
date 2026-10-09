import AlternatingAnalytic.Algebra.FullPolarization
import AlternatingAnalytic.Algebra.DeterminantArray
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Sharp counterexamples to converses of polarization

Lifts of the zero operator family `D = 0` showing that the converses in Proposition B.8 fail:
(Pol1) does not imply (Pw) when `k! = 0` (part 4), and over a finite field `F_q` with
`k ≥ q + 1`, (Pw) does not imply (Pol) (part 3). In both, the nonzero value is the wedge of
the standard basis of `K^k`.

## Main results

- `exists_pol1_not_pw`: Proposition B.8(4).
- `exists_pw_not_pol`: Proposition B.8(3).
-/

noncomputable section
open scoped Classical
open Module

namespace PolarizationCounterexamples

variable {K A J : Type*} [Field K] [AddCommGroup A] [Module K A] {k : ℕ}

/-- Alternating maps `(K^k)^k → Λ^k K^k`. -/
abbrev ExteriorForm (K : Type*) [Field K] (k : ℕ) :=
  (Fin k → K) [⋀^Fin k]→ₗ[K] (⋀[K]^k (Fin k → K))

/-- Lifts in degree `k`: multilinear maps from `A^k` to alternating maps on `K^k`. -/
abbrev ExteriorLift (K A : Type*) [Field K] [AddCommGroup A] [Module K A] (k : ℕ) :=
  MultilinearMap K (fun _ : Fin k => A)
    (ExteriorForm K k)

/-- The standard coordinate vectors. -/
def coordinateBasis (K : Type*) [Field K] (J : Type*) (j : J) : J → K :=
  Pi.single j 1

/-- The wedge `e_1 ∧ ⋯ ∧ e_k` of the standard basis. -/
def standardWedge (K : Type*) [Field K] (k : ℕ) : ⋀[K]^k (Fin k → K) :=
  exteriorPower.ιMulti K k (coordinateBasis K (Fin k))

theorem standardWedge_array (K : Type*) [Field K] (k : ℕ) :
    AlternatingAnalytic.determinantArray (standardWedge K k) id = 1 := by
  rw [standardWedge, AlternatingAnalytic.determinantArray_ιMulti]
  have hm : (fun i j : Fin k => coordinateBasis K (Fin k) j (id i)) =
      (1 : Matrix (Fin k) (Fin k) K) := by
    ext i j
    simp [coordinateBasis, Pi.single_apply, Matrix.one_apply]
  rw [hm, Matrix.det_one]

theorem standardWedge_ne_zero (K : Type*) [Field K] (k : ℕ) : standardWedge K k ≠ 0 := by
  intro hz
  have h := standardWedge_array K k
  rw [hz, map_zero] at h
  exact zero_ne_one h

/-- The lift `θ(a) x_1 ∧ ⋯ ∧ x_k` of a scalar multilinear map `θ`. -/
def scalarExteriorLift (θ : MultilinearMap K (fun _ : Fin k => A) K) : ExteriorLift K A k :=
  θ.smulRight (exteriorPower.ιMulti K k)

@[simp]
theorem scalarExteriorLift_apply (θ : MultilinearMap K (fun _ : Fin k => A) K)
    (a : Fin k → A) (x : Fin k → Fin k → K) :
    scalarExteriorLift θ a x = θ a • exteriorPower.ιMulti K k x := rfl

/-- The lift vanishes when two vector arguments are equal. -/
theorem scalarExteriorLift_alternating (θ : MultilinearMap K (fun _ : Fin k => A) K)
    (a : Fin k → A) (x : Fin k → Fin k → K) (i j : Fin k)
    (h : x i = x j) (hij : i ≠ j) : scalarExteriorLift θ a x = 0 :=
  (scalarExteriorLift θ a).map_eq_zero_of_eq x h hij

/-- The pointwise identity (Pw) for `D = 0`. -/
def ZeroMultiplierPw (Ψ : ExteriorLift K A k) : Prop :=
  ∀ (a : A) (x : Fin k → Fin k → K), Ψ (fun _ => a) x =
    exteriorPower.ιMulti K k (fun i =>
      (0 : A →ₗ[K] ((Fin k → K) →ₗ[K] (Fin k → K))) a (x i))

/-- The identity (Pol1) for `D = 0`. -/
def ZeroMultiplierPol1 (Ψ : ExteriorLift K A k) : Prop :=
  ∀ (b : Fin k → A) (x : Fin k → Fin k → K),
    (∑ σ : Equiv.Perm (Fin k), Ψ (b ∘ σ) x) =
      ∑ σ : Equiv.Perm (Fin k), exteriorPower.ιMulti K k (fun i =>
        (0 : A →ₗ[K] ((Fin k → K) →ₗ[K] (Fin k → K))) (b (σ i)) (x i))

/-- The polarized identity (Pol) for `D = 0`, with labels in a finite type `J`. -/
def ZeroMultiplierPol (J : Type*) [Fintype J] (Ψ : ExteriorLift K A k) : Prop :=
  ∀ (b : J → A) (α : J → ℕ) (_hα : ∑ j, α j = k) (x : Fin k → Fin k → K),
    (MultilinearMap.sumOfType (K := K) (Y := ExteriorForm K k) Ψ b α) x =
      ∑ f ∈ Finset.univ.filter (fun f : Fin k → J => Polarization.selectionType f = α),
        exteriorPower.ιMulti K k (fun i =>
          (0 : A →ₗ[K] ((Fin k → K) →ₗ[K] (Fin k → K))) (b (f i)) (x i))

theorem zero_multiplier_wedge (hk : 0 < k) (a : Fin k → A) (x : Fin k → Fin k → K) :
    exteriorPower.ιMulti K k (fun i =>
      (0 : A →ₗ[K] ((Fin k → K) →ₗ[K] (Fin k → K))) (a i) (x i)) = 0 :=
  (exteriorPower.ιMulti K k).map_coord_zero ⟨0, hk⟩ rfl

/-- The lift `b_1 ⋯ b_k x_1 ∧ ⋯ ∧ x_k` of Proposition B.8(4). -/
def factorialCounterexample (K : Type*) [Field K] (k : ℕ) : ExteriorLift K K k :=
  MultilinearMap.mkPiRing K (Fin k) (exteriorPower.ιMulti K k)

@[simp]
theorem factorialCounterexample_apply (b : Fin k → K) (x : Fin k → Fin k → K) :
    factorialCounterexample K k b x = (∏ i, b i) • exteriorPower.ιMulti K k x := rfl

/-- When `k! = 0`, the lift satisfies (Pol1). -/
theorem factorialCounterexample_pol1 (hfact : (Nat.factorial k : K) = 0) :
    ZeroMultiplierPol1 (factorialCounterexample K k) := by
  have hk : 0 < k := by
    by_contra h
    have : k = 0 := by omega
    subst k
    simp at hfact
  intro b x
  simp only [factorialCounterexample_apply, zero_multiplier_wedge hk, Finset.sum_const_zero]
  rw [← Finset.sum_smul]
  have hs : (∑ σ : Equiv.Perm (Fin k), ∏ i, (b ∘ σ) i) = 0 := by
    simp only [Function.comp_apply, Equiv.prod_comp]
    simp [Fintype.card_perm, nsmul_eq_mul, hfact]
  rw [hs, zero_smul]

/-- The lift takes the nonzero value `e_1 ∧ ⋯ ∧ e_k` on the diagonal `b = (1, …, 1)`. -/
theorem factorialCounterexample_value :
    factorialCounterexample K k (fun _ => 1) (coordinateBasis K (Fin k)) =
      standardWedge K k := by
  simp [factorialCounterexample_apply, standardWedge]

theorem factorialCounterexample_not_pw (hk : 0 < k) :
    ¬ ZeroMultiplierPw (factorialCounterexample K k) := by
  intro h
  have hz := h 1 (coordinateBasis K (Fin k))
  rw [factorialCounterexample_value, zero_multiplier_wedge hk] at hz
  exact standardWedge_ne_zero K k hz

/-- If `k! = 0`, (Pol1) does not imply (Pw) (Proposition B.8(4)). -/
theorem exists_pol1_not_pw (hfact : (Nat.factorial k : K) = 0) :
    ∃ Ψ : ExteriorLift K K k, ZeroMultiplierPol1 Ψ ∧ ¬ ZeroMultiplierPw Ψ := by
  refine ⟨factorialCounterexample K k, factorialCounterexample_pol1 hfact,
    factorialCounterexample_not_pw ?_⟩
  by_contra h
  have : k = 0 := by omega
  subst k
  simp at hfact

/-- The multilinear map `a ↦ ∏ i, a i (p i)`. -/
def coordinateProduct (p : Fin k → J) :
    MultilinearMap K (fun _ : Fin k => J → K) K :=
  (MultilinearMap.mkPiAlgebra K (Fin k) K).compLinearMap fun i => LinearMap.proj (p i)

@[simp]
theorem coordinateProduct_apply (p : Fin k → J) (a : Fin k → J → K) :
    coordinateProduct (K := K) p a = ∏ i, a i (p i) := rfl

/-- On basis vectors, `coordinateProduct p` detects the pattern `p`. -/
theorem coordinateProduct_basis (p f : Fin k → J) :
    coordinateProduct (K := K) p (fun i => coordinateBasis K J (f i)) =
      if f = p then 1 else 0 := by
  simp [coordinateProduct_apply, coordinateBasis, Pi.single_apply, Fintype.prod_boole,
    funext_iff, eq_comm]

/-- The grouped coefficient of a coordinate product is a Kronecker delta. -/
theorem coordinateProduct_sumOfType [Fintype J] (p : Fin k → J) (α : J → ℕ) :
    (coordinateProduct (K := K) p).sumOfType (coordinateBasis K J) α =
      if Polarization.selectionType p = α then 1 else 0 := by
  simp only [MultilinearMap.sumOfType, coordinateProduct_basis]
  simp

/-- First monomial pattern: q copies of coordinate 0, one copy of coordinate 1,
then r copies of coordinate 2. -/
def firstPattern (q r : ℕ) : Fin (q + 1 + r) → Fin 3 :=
  Fin.append (Fin.snoc (fun _ : Fin q => 0) 1) (fun _ : Fin r => 2)

/-- Second monomial pattern: one copy of coordinate 0, q copies of coordinate 1,
then r copies of coordinate 2. -/
def secondPattern (q r : ℕ) : Fin (q + 1 + r) → Fin 3 :=
  Fin.append (Fin.cons 0 (fun _ : Fin q => 1)) (fun _ : Fin r => 2)

theorem firstPattern_product (q r : ℕ) (a : Fin 3 → K) :
    (∏ i, a (firstPattern q r i)) = (a 0 ^ q * a 1) * a 2 ^ r := by
  rw [Fin.prod_univ_add]
  simp only [firstPattern, Fin.append_left, Fin.append_right]
  rw [Fin.prod_univ_castSucc]
  simp

theorem secondPattern_product (q r : ℕ) (a : Fin 3 → K) :
    (∏ i, a (secondPattern q r i)) = (a 0 * a 1 ^ q) * a 2 ^ r := by
  rw [Fin.prod_univ_add]
  simp only [secondPattern, Fin.append_left, Fin.append_right]
  rw [Fin.prod_univ_succ]
  simp

theorem selectionType_eq_sum [Fintype J] (p : Fin k → J) (j : J) :
    Polarization.selectionType p j = ∑ i, if p i = j then 1 else 0 := by
  simp [Polarization.selectionType]

theorem firstPattern_type_zero (q r : ℕ) :
    Polarization.selectionType (firstPattern q r) 0 = q := by
  rw [selectionType_eq_sum, Fin.sum_univ_add]
  simp only [firstPattern, Fin.append_left, Fin.append_right]
  rw [Fin.sum_univ_castSucc]
  simp

theorem secondPattern_type_zero (q r : ℕ) :
    Polarization.selectionType (secondPattern q r) 0 = 1 := by
  rw [selectionType_eq_sum, Fin.sum_univ_add]
  simp only [secondPattern, Fin.append_left, Fin.append_right]
  rw [Fin.sum_univ_succ]
  simp

theorem pattern_types_ne (q r : ℕ) (hq : 1 < q) :
    Polarization.selectionType (secondPattern q r) ≠ Polarization.selectionType (firstPattern q r) := by
  intro h
  have := congrFun h 0
  rw [firstPattern_type_zero, secondPattern_type_zero] at this
  omega

/-- Grouped sums of `scalarExteriorLift θ` are the grouped sums of `θ` times the wedge. -/
theorem scalarExteriorLift_sumOfType [Fintype J]
    (θ : MultilinearMap K (fun _ : Fin k => A) K) (b : J → A) (α : J → ℕ) :
    MultilinearMap.sumOfType (K := K) (Y := ExteriorForm K k) (scalarExteriorLift θ) b α =
      θ.sumOfType b α • exteriorPower.ιMulti K k := by
  simp only [MultilinearMap.sumOfType, scalarExteriorLift, MultilinearMap.smulRight_apply,
    Finset.sum_smul]

/-- The form `θ` of Proposition B.8(3), with `q = card K` and `r = k - q - 1`. -/
def finiteScalarCounterexample (K : Type*) [Field K] [Fintype K] (r : ℕ) :
    MultilinearMap K (fun _ : Fin (Fintype.card K + 1 + r) => Fin 3 → K) K :=
  coordinateProduct (firstPattern (Fintype.card K) r) -
    coordinateProduct (secondPattern (Fintype.card K) r)

/-- `θ` vanishes on the diagonal, since `c^q = c` in `F_q`. -/
theorem finiteScalarCounterexample_diagonal [Fintype K] (r : ℕ) (a : Fin 3 → K) :
    finiteScalarCounterexample K r (fun _ => a) = 0 := by
  change (∏ i, a (firstPattern (Fintype.card K) r i)) -
    (∏ i, a (secondPattern (Fintype.card K) r i)) = 0
  rw [firstPattern_product, secondPattern_product,
    FiniteField.pow_card, FiniteField.pow_card, sub_self]

/-- The grouped coefficient of `θ` of type `(q, 1, r)` is `1`. -/
theorem finiteScalarCounterexample_grouped [Fintype K] (r : ℕ) :
    (finiteScalarCounterexample K r).sumOfType (coordinateBasis K (Fin 3))
      (Polarization.selectionType (firstPattern (Fintype.card K) r)) = 1 := by
  have hne := pattern_types_ne (Fintype.card K) r (Fintype.one_lt_card (α := K))
  change (coordinateProduct (K := K) (firstPattern (Fintype.card K) r) -
    coordinateProduct (secondPattern (Fintype.card K) r)).sumOfType _ _ = 1
  simp only [MultilinearMap.sumOfType, sub_apply, Finset.sum_sub_distrib]
  change (coordinateProduct (K := K) (firstPattern (Fintype.card K) r)).sumOfType _ _ -
    (coordinateProduct (K := K) (secondPattern (Fintype.card K) r)).sumOfType _ _ = 1
  rw [coordinateProduct_sumOfType, coordinateProduct_sumOfType, ite_eq_left rfl, ite_eq_right hne, sub_zero]

/-- The lift `Θ(a; x) = θ(a) x_1 ∧ ⋯ ∧ x_k` of Proposition B.8(3), in degree `q + 1 + r`. -/
def finiteCounterexample (K : Type*) [Field K] [Fintype K] (r : ℕ) :
    ExteriorLift K (Fin 3 → K) (Fintype.card K + 1 + r) :=
  scalarExteriorLift (finiteScalarCounterexample K r)

/-- `Θ` satisfies (Pw). -/
theorem finiteCounterexample_pw [Fintype K] (r : ℕ) :
    ZeroMultiplierPw (finiteCounterexample K r) := by
  intro a x
  change scalarExteriorLift (finiteScalarCounterexample K r) (fun _ => a) x = _
  rw [scalarExteriorLift_apply, finiteScalarCounterexample_diagonal, zero_smul,
    zero_multiplier_wedge (by omega)]

/-- The grouped coefficient of `Θ` of type `(q, 1, r)` is `e_1 ∧ ⋯ ∧ e_k`. -/
theorem finiteCounterexample_grouped [Fintype K] (r : ℕ) :
    (MultilinearMap.sumOfType (K := K)
      (Y := ExteriorForm K (Fintype.card K + 1 + r)) (finiteCounterexample K r)
      (coordinateBasis K (Fin 3)) (Polarization.selectionType (firstPattern (Fintype.card K) r)))
      (coordinateBasis K (Fin (Fintype.card K + 1 + r))) =
        standardWedge K (Fintype.card K + 1 + r) := by
  rw [finiteCounterexample, scalarExteriorLift_sumOfType, finiteScalarCounterexample_grouped]
  simp only [one_smul, standardWedge]

theorem finiteCounterexample_not_pol [Fintype K] (r : ℕ) :
    ¬ ZeroMultiplierPol (Fin 3) (finiteCounterexample K r) := by
  intro h
  have hz := h (coordinateBasis K (Fin 3))
    (Polarization.selectionType (firstPattern (Fintype.card K) r))
    (Polarization.sum_selectionType _)
    (coordinateBasis K (Fin (Fintype.card K + 1 + r)))
  rw [finiteCounterexample_grouped] at hz
  have hk : 0 < Fintype.card K + 1 + r := by omega
  simp only [zero_multiplier_wedge hk, Finset.sum_const_zero] at hz
  exact standardWedge_ne_zero K _ hz

/-- Over `F_q` with `k ≥ q + 1`, (Pw) does not imply (Pol) (Proposition B.8(3)). -/
theorem exists_pw_not_pol [Fintype K] (hk : Fintype.card K + 1 ≤ k) :
    ∃ Ψ : ExteriorLift K (Fin 3 → K) k,
      ZeroMultiplierPw Ψ ∧ ¬ ZeroMultiplierPol (Fin 3) Ψ := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hk
  exact ⟨finiteCounterexample K r, finiteCounterexample_pw r, finiteCounterexample_not_pol r⟩


end PolarizationCounterexamples
