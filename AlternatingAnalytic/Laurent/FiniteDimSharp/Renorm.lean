import AlternatingAnalytic.Laurent.FiniteDimSharp.Orthonormal
import AlternatingAnalytic.Analysis.DiscreteNormRounding
import AlternatingAnalytic.Analysis.LaurentField

/-!
# Complemented copies of `c₀(ℕ, K)` in infinite-dimensional nonarchimedean Banach spaces

Let `K` be a complete ultrametric field whose nonzero norms are the integral powers of `e > 1`,
all of which occur, and let `P` be an infinite-dimensional `K`-Banach space with an equivalent
ultrametric norm. Rounding that norm to `e ^ ℤ` (`HasEquivalentUltrametricNorm.exists_discrete`)
and passing to the type synonym `Renormed q` carrying it, the orthonormal-sequence construction
gives a linear isometry `C₀(ℕ, K) → Renormed q`, and Ingleton's theorem a contracting left inverse. Transported
back to `P`, this gives bounded `ι : C₀(ℕ, K) → P` and `π : P → C₀(ℕ, K)` with `π ∘ ι = id`
(`exists_cZero_retraction_of_discrete`), the part of Serre's orthonormal-basis theorem used in
Corollary C.8. `K = κ((X))` satisfies the hypotheses with `e = r⁻¹` (`laurent_norm_mem_zpowers`,
`laurent_exists_norm_eq_zpow`).
-/

set_option backward.isDefEq.respectTransparency false

open scoped NNReal ZeroAtInfty

namespace AlternatingAnalytic.FiniteDimSharp

/-- A type synonym for `P`, to carry the seminorm `q` as its norm. -/
@[nolint unusedArguments]
def Renormed {K P : Type*} [NormedField K] [AddCommGroup P] [Module K P] (_q : Seminorm K P) :
    Type _ :=
  P

namespace Renormed

variable {K P : Type*} [NontriviallyNormedField K] [AddCommGroup P] [Module K P]
  (q : Seminorm K P)

instance : AddCommGroup (Renormed q) := inferInstanceAs (AddCommGroup P)

instance : Module K (Renormed q) := inferInstanceAs (Module K P)

/-- The identity of `P` as a linear equivalence onto the synonym. -/
def equiv : P ≃ₗ[K] Renormed q := LinearEquiv.refl K P

/-- The normed group structure given by a seminorm that vanishes only at zero. -/
noncomputable abbrev normedAddCommGroup (h0 : ∀ x, q x = 0 → x = 0) :
    NormedAddCommGroup (Renormed q) :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun := fun x => q x
      map_zero' := map_zero q
      add_le' := map_add_le_add q
      neg' := map_neg_eq_map q
      eq_zero_of_map_eq_zero' := h0 }

/-- The normed space structure given by a seminorm that vanishes only at zero. -/
noncomputable abbrev normedSpace (h0 : ∀ x, q x = 0 → x = 0) :
    letI := normedAddCommGroup q h0
    NormedSpace K (Renormed q) :=
  letI := normedAddCommGroup q h0
  { norm_smul_le := fun c x => (map_smul_eq_mul q c x).le }

end Renormed

section Discrete

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
  {e : ℝ}

/-- An infinite-dimensional Banach space with an equivalent ultrametric norm over a complete
discretely valued field contains a complemented copy of `C₀(ℕ, K)`. -/
theorem exists_cZero_retraction_of_discrete (he : 1 < e)
    (hval : ∀ c : K, c ≠ 0 → ∃ n : ℤ, ‖c‖ = e ^ n) (hK : ∀ n : ℤ, ∃ c : K, ‖c‖ = e ^ n)
    {P : Type*} [NormedAddCommGroup P] [NormedSpace K P] [CompleteSpace P]
    (hP : HasEquivalentUltrametricNorm K P) (hinf : ¬ FiniteDimensional K P) :
    ∃ (ι : C₀(ℕ, K) →L[K] P) (π : P →L[K] C₀(ℕ, K)), ∀ a, π (ι a) = a := by
  obtain ⟨q, hq, ⟨A, hA, hlow⟩, ⟨B, hB, hup⟩, hdisc⟩ := hP.exists_discrete he hval
  have h0 : ∀ x : P, q x = 0 → x = 0 := fun x hx =>
    norm_le_zero_iff.mp ((hlow x).trans (by rw [hx, mul_zero]))
  let : NormedAddCommGroup (Renormed q) := Renormed.normedAddCommGroup q h0
  let : NormedSpace K (Renormed q) := Renormed.normedSpace q h0
  have : IsUltrametricDist (Renormed q) :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y => hq x y
  let T : P ≃L[K] Renormed q :=
    (Renormed.equiv q).toContinuousLinearEquivOfBounds B A (fun x => hup x) (fun x => hlow x)
  have : CompleteSpace (Renormed q) :=
    (completeSpace_congr (e := T.toLinearEquiv.toEquiv) T.isUniformEmbedding).mp inferInstance
  have hinf' : ¬ FiniteDimensional K (Renormed q) := fun h =>
    hinf (T.symm.toLinearEquiv.finiteDimensional)
  obtain ⟨v, hv1, hv2⟩ :=
    exists_orthonormal_seq (K := K) (X := Renormed q) he (fun x hx => hdisc x hx) hK hinf'
  obtain ⟨ι', -⟩ := exists_cZero_linearIsometry v hv1 hv2
  have := sphericallyCompleteSpace_cZero (K := K) he hval
  obtain ⟨π', -, hπ'⟩ := exists_retraction_of_linearIsometry ι'
  refine ⟨T.symm.toContinuousLinearMap.comp ι'.toContinuousLinearMap,
    π'.comp T.toContinuousLinearMap, fun a => ?_⟩
  simp [hπ']

end Discrete

section Laurent

variable (κ : Type*) [Field κ] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)]

/-- The radius `r ∈ (0, 1)` has `1 < r⁻¹`. -/
theorem one_lt_inv_radius : 1 < ((r : ℝ))⁻¹ :=
  (one_lt_inv₀ (NNReal.coe_pos.mpr Fact.out)).mpr (NNReal.coe_lt_one.mpr Fact.out)

/-- Nonzero norms of `κ((X))` are integral powers of `r⁻¹`. -/
theorem laurent_norm_mem_zpowers (c : LaurentField κ r) (hc : c ≠ 0) :
    ∃ n : ℤ, ‖c‖ = ((r : ℝ))⁻¹ ^ n :=
  ⟨-(show LaurentSeries κ from c).order, by
    rw [LaurentField.norm_of_ne_zero κ r c hc, inv_zpow', neg_neg]⟩

/-- Every integral power of `r⁻¹` is the norm of a monomial of `κ((X))`. -/
theorem laurent_exists_norm_eq_zpow (n : ℤ) : ∃ c : LaurentField κ r, ‖c‖ = ((r : ℝ))⁻¹ ^ n := by
  have h1 : (HahnSeries.single (-n) (1 : κ) : LaurentSeries κ) ≠ 0 :=
    HahnSeries.single_ne_zero one_ne_zero
  refine ⟨(HahnSeries.single (-n) (1 : κ) : LaurentSeries κ), ?_⟩
  rw [LaurentField.norm_of_ne_zero κ r _ h1, HahnSeries.order_single one_ne_zero, inv_zpow']

end Laurent

end AlternatingAnalytic.FiniteDimSharp
