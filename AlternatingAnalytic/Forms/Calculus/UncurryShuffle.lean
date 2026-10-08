import AlternatingAnalytic.Forms.Calculus.ShuffleIdentities

/-!
# The algebraic Leibniz rule for the shuffle product

For a linear map `A : M → Alt^k(M; R)`, the signed sum `∑ᵢ (-1)^i A(vᵢ)(v₀, …, v̂ᵢ, …)` is
`alternatizeUncurryFin A`. This file proves the two algebraic identities behind the Leibniz rule
`d(η ∧ ζ) = dη ∧ ζ + (-1)^k η ∧ dζ`:
`∑ᵢ (-1)^i (A(vᵢ) ∧ ζ)(v̂ᵢ) = (alternatizeUncurryFin A ∧ ζ)(v)` (`sum_shuffle_left_removeNth`) and
`∑ᵢ (-1)^i (μ ∧ B(vᵢ))(v̂ᵢ) = (-1)^k (μ ∧ alternatizeUncurryFin B)(v)`
(`sum_shuffle_right_removeNth`). For `A = φ ⊗ μ` of rank one they follow from
`alternatizeUncurryFin_smulRight`, associativity and graded commutativity. The general case
pulls `A` back along `tupleMap v` to `Fin N → R`, where it is a finite sum of rank-one maps.
-/

open Equiv

namespace AlternatingAnalytic.Forms

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {k l : ℕ}

/-- Pullback of alternating maps along a linear map, as a linear map. -/
noncomputable def compLinearMapₗ {M' N : Type*} [AddCommGroup M'] [Module R M'] [AddCommGroup N]
    [Module R N] {ι : Type*} (g : M' →ₗ[R] M) : (M [⋀^ι]→ₗ[R] N) →ₗ[R] (M' [⋀^ι]→ₗ[R] N) where
  toFun f := f.compLinearMap g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem compLinearMapₗ_apply {M' N : Type*} [AddCommGroup M'] [Module R M'] [AddCommGroup N]
    [Module R N] {ι : Type*} (g : M' →ₗ[R] M) (f : M [⋀^ι]→ₗ[R] N) :
    compLinearMapₗ g f = f.compLinearMap g :=
  rfl

/-- `alternatizeUncurryFin` commutes with pullback along linear maps. -/
theorem alternatizeUncurryFin_compLinearMap {M' : Type*} [AddCommGroup M'] [Module R M']
    (A : M →ₗ[R] M [⋀^Fin k]→ₗ[R] R) (g : M' →ₗ[R] M) :
    (AlternatingMap.alternatizeUncurryFin A).compLinearMap g =
      AlternatingMap.alternatizeUncurryFin (compLinearMapₗ g ∘ₗ A ∘ₗ g) := by
  ext w
  simp only [AlternatingMap.compLinearMap_apply, AlternatingMap.alternatizeUncurryFin_apply,
    LinearMap.comp_apply, compLinearMapₗ_apply]
  rfl

/-- Evaluation of a finite sum of alternating maps. -/
theorem alternatingMap_sum_apply {N : Type*} [AddCommGroup N] [Module R N] {ι κ : Type*}
    (s : Finset κ) (f : κ → M [⋀^ι]→ₗ[R] N) (v : ι → M) :
    (∑ j ∈ s, f j) v = ∑ j ∈ s, f j v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => simp [Finset.sum_insert hj, AlternatingMap.add_apply, ih]

/-- `alternatizeUncurryFin` commutes with finite sums. -/
theorem alternatizeUncurryFin_sum {ι : Type*} (s : Finset ι)
    (f : ι → M →ₗ[R] M [⋀^Fin k]→ₗ[R] R) :
    AlternatingMap.alternatizeUncurryFin (∑ j ∈ s, f j) =
      ∑ j ∈ s, AlternatingMap.alternatizeUncurryFin (f j) :=
  map_sum AlternatingMap.alternatizeUncurryFinLM f s

/-- A linear map on `Fin N → R` is the sum of the rank-one maps given by its values on the
standard basis. -/
theorem linearMap_eq_sum_smulRight {N : ℕ} {X : Type*} [AddCommGroup X] [Module R X]
    (A : (Fin N → R) →ₗ[R] X) :
    A = ∑ j, (LinearMap.proj j : (Fin N → R) →ₗ[R] R).smulRight (A (Pi.single j 1)) := by
  classical
  refine (Pi.basisFun R (Fin N)).ext fun i => ?_
  simp [Pi.single_apply]

/-- `alternatizeUncurryFin (φ ⊗ μ)` is the reindexed shuffle product `φ ∧ μ`. -/
theorem alternatizeUncurryFin_smulRight_eq (φ : M →ₗ[R] R) (μ : M [⋀^Fin k]→ₗ[R] R) :
    AlternatingMap.alternatizeUncurryFin (φ.smulRight μ) =
      (shuffle (AlternatingMap.ofSubsingleton R M R (0 : Fin 1) φ) μ).domDomCongr
        (finCongr (Nat.add_comm 1 k)) := by
  ext u
  rw [alternatizeUncurryFin_smulRight, AlternatingMap.domDomCongr_apply]

/-- The first algebraic Leibniz identity for a rank-one `A = φ ⊗ μ`. -/
theorem sum_shuffle_left_removeNth_smulRight (φ : M →ₗ[R] R) (μ : M [⋀^Fin k]→ₗ[R] R)
    (ζ : M [⋀^Fin l]→ₗ[R] R) (v : Fin (k + l + 1) → M) :
    ∑ i : Fin (k + l + 1),
        (-1 : ℤ) ^ (i : ℕ) • shuffle (φ.smulRight μ (v i)) ζ (Fin.removeNth i v) =
      shuffle (AlternatingMap.alternatizeUncurryFin (φ.smulRight μ)) ζ
        (v ∘ finCongr (by omega : k + 1 + l = k + l + 1)) := by
  have hL : ∑ i : Fin (k + l + 1),
        (-1 : ℤ) ^ (i : ℕ) • shuffle (φ.smulRight μ (v i)) ζ (Fin.removeNth i v) =
      AlternatingMap.alternatizeUncurryFin (φ.smulRight (shuffle μ ζ)) v := by
    simp [AlternatingMap.alternatizeUncurryFin_apply, shuffle_smul_left]
  rw [hL, alternatizeUncurryFin_smulRight, alternatizeUncurryFin_smulRight_eq,
    shuffle_domDomCongr_finCongr_left, shuffle_assoc]
  rfl

/-- The second algebraic Leibniz identity for a rank-one `B = φ ⊗ ν`. -/
theorem sum_shuffle_right_removeNth_smulRight (φ : M →ₗ[R] R) (μ : M [⋀^Fin k]→ₗ[R] R)
    (ν : M [⋀^Fin l]→ₗ[R] R) (v : Fin (k + l + 1) → M) :
    ∑ i : Fin (k + l + 1),
        (-1 : ℤ) ^ (i : ℕ) • shuffle μ (φ.smulRight ν (v i)) (Fin.removeNth i v) =
      (-1 : R) ^ k • shuffle μ (AlternatingMap.alternatizeUncurryFin (φ.smulRight ν))
        (v ∘ finCongr (by omega : k + (l + 1) = k + l + 1)) := by
  have hL : ∑ i : Fin (k + l + 1),
        (-1 : ℤ) ^ (i : ℕ) • shuffle μ (φ.smulRight ν (v i)) (Fin.removeNth i v) =
      AlternatingMap.alternatizeUncurryFin (φ.smulRight (shuffle μ ν)) v := by
    simp [AlternatingMap.alternatizeUncurryFin_apply, shuffle_smul_right]
  set φ₁ := AlternatingMap.ofSubsingleton R M R (0 : Fin 1) φ
  have h1 : shuffle φ₁ (shuffle μ ν) (v ∘ finCongr (Nat.add_comm 1 (k + l))) =
      shuffle (shuffle φ₁ μ) ν (v ∘ finCongr (by omega : 1 + k + l = k + l + 1)) :=
    (shuffle_assoc φ₁ μ ν (v ∘ finCongr (by omega : 1 + k + l = k + l + 1))).symm
  rw [hL, alternatizeUncurryFin_smulRight, h1, shuffle_comm' φ₁ μ, shuffle_smul_left,
    AlternatingMap.smul_apply, shuffle_domDomCongr_finCongr_left, shuffle_assoc,
    alternatizeUncurryFin_smulRight_eq, shuffle_domDomCongr_finCongr_right, one_mul]
  rfl

/-- The first algebraic Leibniz identity. -/
theorem sum_shuffle_left_removeNth (A : M →ₗ[R] M [⋀^Fin k]→ₗ[R] R) (ζ : M [⋀^Fin l]→ₗ[R] R)
    (v : Fin (k + l + 1) → M) :
    ∑ i : Fin (k + l + 1), (-1 : ℤ) ^ (i : ℕ) • shuffle (A (v i)) ζ (Fin.removeNth i v) =
      shuffle (AlternatingMap.alternatizeUncurryFin A) ζ
        (v ∘ finCongr (by omega : k + 1 + l = k + l + 1)) := by
  set L := tupleMap (R := R) v
  set A' := compLinearMapₗ L ∘ₗ A ∘ₗ L
  have hL : ∑ i : Fin (k + l + 1), (-1 : ℤ) ^ (i : ℕ) • shuffle (A (v i)) ζ (Fin.removeNth i v) =
      ∑ i : Fin (k + l + 1), (-1 : ℤ) ^ (i : ℕ) • shuffle (A' (Pi.single i 1)) (ζ.compLinearMap L)
        (Fin.removeNth i
          (fun j : Fin (k + l + 1) => (Pi.single j (1 : R) : Fin (k + l + 1) → R))) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [A', LinearMap.comp_apply, compLinearMapₗ_apply,
      shuffle_compLinearMap, AlternatingMap.compLinearMap_apply, Fin.removeNth_apply, L,
      tupleMap_single]
    rfl
  rw [hL, ← compLinearMap_tupleMap_apply (R := R), ← shuffle_compLinearMap,
    alternatizeUncurryFin_compLinearMap]
  change _ = shuffle (AlternatingMap.alternatizeUncurryFin A') _ _
  rw [linearMap_eq_sum_smulRight A']
  simp only [LinearMap.coe_sum, Finset.sum_apply, shuffle_sum_left, alternatingMap_sum_apply,
    Finset.smul_sum,
    alternatizeUncurryFin_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact sum_shuffle_left_removeNth_smulRight _ _ _ _

/-- The second algebraic Leibniz identity. -/
theorem sum_shuffle_right_removeNth (μ : M [⋀^Fin k]→ₗ[R] R) (B : M →ₗ[R] M [⋀^Fin l]→ₗ[R] R)
    (v : Fin (k + l + 1) → M) :
    ∑ i : Fin (k + l + 1), (-1 : ℤ) ^ (i : ℕ) • shuffle μ (B (v i)) (Fin.removeNth i v) =
      (-1 : R) ^ k • shuffle μ (AlternatingMap.alternatizeUncurryFin B)
        (v ∘ finCongr (by omega : k + (l + 1) = k + l + 1)) := by
  set L := tupleMap (R := R) v
  set B' := compLinearMapₗ L ∘ₗ B ∘ₗ L
  have hL : ∑ i : Fin (k + l + 1), (-1 : ℤ) ^ (i : ℕ) • shuffle μ (B (v i)) (Fin.removeNth i v) =
      ∑ i : Fin (k + l + 1), (-1 : ℤ) ^ (i : ℕ) • shuffle (μ.compLinearMap L) (B' (Pi.single i 1))
        (Fin.removeNth i
          (fun j : Fin (k + l + 1) => (Pi.single j (1 : R) : Fin (k + l + 1) → R))) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [B', LinearMap.comp_apply, compLinearMapₗ_apply,
      shuffle_compLinearMap, AlternatingMap.compLinearMap_apply, Fin.removeNth_apply, L,
      tupleMap_single]
    rfl
  rw [hL, ← compLinearMap_tupleMap_apply (R := R), ← shuffle_compLinearMap,
    alternatizeUncurryFin_compLinearMap]
  change _ = (-1 : R) ^ k • shuffle _ (AlternatingMap.alternatizeUncurryFin B') _
  rw [linearMap_eq_sum_smulRight B']
  simp only [LinearMap.coe_sum, Finset.sum_apply, shuffle_sum_right,
    alternatingMap_sum_apply, Finset.smul_sum,
    alternatizeUncurryFin_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact sum_shuffle_right_removeNth_smulRight _ _ _ _

end AlternatingAnalytic.Forms
