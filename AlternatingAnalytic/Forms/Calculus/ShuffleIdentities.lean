import AlternatingAnalytic.Forms.Calculus.Shuffle
import AlternatingAnalytic.Forms.Calculus.Representation

/-!
# Identities of the shuffle product

The unit laws, associativity and graded commutativity of the shuffle product of scalar
alternating maps, and the expression of `alternatizeUncurryFin (φ.smulRight θ)` as the shuffle
product of the `1`-form `φ` with `θ`. Each identity is evaluated at a tuple `v`; pulling back
along `tupleMap v` reduces it to an identity between alternatizations on `Fin N → R`. No factorial
is inverted, so the identities hold over every commutative ring.
-/

open Equiv

namespace AlternatingAnalytic.Forms

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {k l m : ℕ}

/-- The pullback of the constant `0`-form `1` is `1`. -/
theorem constOfIsEmpty_compLinearMap {M' : Type*} [AddCommGroup M'] [Module R M']
    (g : M' →ₗ[R] M) :
    (AlternatingMap.constOfIsEmpty R M (Fin 0) (1 : R)).compLinearMap g =
      AlternatingMap.constOfIsEmpty R M' (Fin 0) (1 : R) := by
  ext v
  simp

/-- The pullback of a `1`-form is the `1`-form of the composite. -/
theorem ofSubsingleton_compLinearMap {M' : Type*} [AddCommGroup M'] [Module R M']
    (φ : M →ₗ[R] R) (g : M' →ₗ[R] M) :
    (AlternatingMap.ofSubsingleton R M R (0 : Fin 1) φ).compLinearMap g =
      AlternatingMap.ofSubsingleton R M' R (0 : Fin 1) (φ ∘ₗ g) := by
  ext v
  simp

/-- A `1`-ary multilinear map is its own alternatization. -/
theorem alternatization_ofSubsingleton (φ : M →ₗ[R] R) :
    MultilinearMap.alternatization (MultilinearMap.ofSubsingleton R M R (0 : Fin 1) φ) =
      AlternatingMap.ofSubsingleton R M R (0 : Fin 1) φ := by
  ext v
  simp [MultilinearMap.alternatization_apply]

/-- The constant `0`-form `1` is a left unit for the shuffle product. -/
theorem shuffle_constOfIsEmpty_left (μ : M [⋀^Fin k]→ₗ[R] R) (v : Fin (0 + k) → M) :
    shuffle (AlternatingMap.constOfIsEmpty R M (Fin 0) (1 : R)) μ v =
      μ (v ∘ finCongr (Nat.zero_add k).symm) := by
  obtain ⟨a, ha⟩ := exists_alternatization_eq (μ.compLinearMap (tupleMap (R := R) v))
  rw [← compLinearMap_tupleMap_apply_self (R := R), ← compLinearMap_tupleMap_apply (R := R),
    ← shuffle_compLinearMap, constOfIsEmpty_compLinearMap, ← ha,
    ← alternatization_constOfIsEmpty, shuffle_alternatization, constOfIsEmpty_mulProd,
    alternatization_domDomCongr]
  rfl

/-- The constant `0`-form `1` is a right unit for the shuffle product. -/
theorem shuffle_constOfIsEmpty_right (μ : M [⋀^Fin k]→ₗ[R] R) (v : Fin (k + 0) → M) :
    shuffle μ (AlternatingMap.constOfIsEmpty R M (Fin 0) (1 : R)) v =
      μ (v ∘ finCongr (Nat.add_zero k).symm) := by
  obtain ⟨a, ha⟩ := exists_alternatization_eq (μ.compLinearMap (tupleMap (R := R) v))
  rw [← compLinearMap_tupleMap_apply_self (R := R), ← compLinearMap_tupleMap_apply (R := R),
    ← shuffle_compLinearMap, constOfIsEmpty_compLinearMap, ← ha,
    ← alternatization_constOfIsEmpty, shuffle_alternatization, mulProd_constOfIsEmpty,
    alternatization_domDomCongr]
  rfl

/-- The shuffle product is associative. -/
theorem shuffle_assoc (μ : M [⋀^Fin k]→ₗ[R] R) (ν : M [⋀^Fin l]→ₗ[R] R)
    (θ : M [⋀^Fin m]→ₗ[R] R) (v : Fin (k + l + m) → M) :
    shuffle (shuffle μ ν) θ v =
      shuffle μ (shuffle ν θ) (v ∘ finCongr (Nat.add_assoc k l m).symm) := by
  obtain ⟨a, ha⟩ := exists_alternatization_eq (μ.compLinearMap (tupleMap (R := R) v))
  obtain ⟨b, hb⟩ := exists_alternatization_eq (ν.compLinearMap (tupleMap (R := R) v))
  obtain ⟨c, hc⟩ := exists_alternatization_eq (θ.compLinearMap (tupleMap (R := R) v))
  rw [← compLinearMap_tupleMap_apply_self (R := R), ← compLinearMap_tupleMap_apply (R := R),
    ← shuffle_compLinearMap, ← shuffle_compLinearMap, ← shuffle_compLinearMap,
    ← shuffle_compLinearMap, ← ha, ← hb, ← hc, shuffle_alternatization, shuffle_alternatization,
    shuffle_alternatization, shuffle_alternatization, mulProd_assoc, alternatization_domDomCongr]
  rfl

/-- Swapping the factors of a shuffle product reindexes it by `finAddFlip`. -/
theorem shuffle_swap (μ : M [⋀^Fin k]→ₗ[R] R) (ν : M [⋀^Fin l]→ₗ[R] R) :
    shuffle ν μ = (shuffle μ ν).domDomCongr finAddFlip := by
  ext v
  obtain ⟨a, ha⟩ := exists_alternatization_eq (μ.compLinearMap (tupleMap (R := R) v))
  obtain ⟨b, hb⟩ := exists_alternatization_eq (ν.compLinearMap (tupleMap (R := R) v))
  rw [AlternatingMap.domDomCongr_apply, ← compLinearMap_tupleMap_apply_self (R := R),
    ← compLinearMap_tupleMap_apply (R := R), ← shuffle_compLinearMap, ← shuffle_compLinearMap,
    ← ha, ← hb, shuffle_alternatization, shuffle_alternatization, mulProd_comm,
    alternatization_domDomCongr]
  rfl

/-- The `m`-th power of `finRotate n` adds `m` modulo `n`. -/
theorem val_finRotate_pow (n m : ℕ) (i : Fin n) : (((finRotate n) ^ m) i : ℕ) = (i + m) % n := by
  induction m with
  | zero => simp [Nat.mod_eq_of_lt i.isLt]
  | succ m ih =>
    cases n with
    | zero => exact i.elim0
    | succ n =>
      rw [pow_succ', Perm.mul_apply, finRotate_apply, Fin.val_add, ih, Fin.val_one',
        ← Nat.add_mod, Nat.add_assoc]

/-- The block swap `Fin (k + l) → Fin (l + k) = Fin (k + l)` has sign `(-1)^(k l)`. -/
theorem sign_finAddFlip_trans_finCongr (k l : ℕ) :
    Perm.sign (finAddFlip.trans (finCongr (Nat.add_comm l k)) : Perm (Fin (k + l))) =
      (-1) ^ (k * l) := by
  have hπ : (finAddFlip.trans (finCongr (Nat.add_comm l k)) : Perm (Fin (k + l))) =
      finRotate (k + l) ^ l := by
    ext i
    rw [val_finRotate_pow]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Equiv.trans_apply, finAddFlip_apply_castAdd, finCongr_apply, Fin.val_cast,
        Fin.val_natAdd, Fin.val_castAdd]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · simp only [Equiv.trans_apply, finAddFlip_apply_natAdd, finCongr_apply, Fin.val_cast,
        Fin.val_natAdd, Fin.val_castAdd]
      rw [show k + j + l = j + (k + l) by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨t, ht⟩ := Nat.even_mul_pred_self l
  have hexp : (k + l - 1) * l = k * l + (t + t) := by
    rcases Nat.eq_zero_or_pos l with rfl | hl
    · simp at ht ⊢
      omega
    · rw [show k + l - 1 = k + (l - 1) by omega, add_mul, ← ht, mul_comm (l - 1) l]
  rw [hπ, map_pow, sign_finRotate, ← pow_mul, hexp, pow_add, Even.neg_one_pow ⟨t, rfl⟩, mul_one]

/-- The shuffle product is graded commutative. -/
theorem shuffle_comm (μ : M [⋀^Fin k]→ₗ[R] R) (ν : M [⋀^Fin l]→ₗ[R] R) (v : Fin (k + l) → M) :
    shuffle μ ν v = (-1 : R) ^ (k * l) * shuffle ν μ (v ∘ finCongr (Nat.add_comm l k)) := by
  rw [shuffle_swap μ ν, AlternatingMap.domDomCongr_apply]
  have : (v ∘ finCongr (Nat.add_comm l k)) ∘ finAddFlip =
      v ∘ (finAddFlip.trans (finCongr (Nat.add_comm l k)) : Perm (Fin (k + l))) := rfl
  rw [this, AlternatingMap.map_perm, sign_finAddFlip_trans_finCongr, Units.smul_def,
    zsmul_eq_mul, ← mul_assoc]
  push_cast
  rw [← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]

/-- The shuffle product is graded commutative, as an identity of alternating maps. -/
theorem shuffle_comm' (μ : M [⋀^Fin k]→ₗ[R] R) (ν : M [⋀^Fin l]→ₗ[R] R) :
    shuffle μ ν = (-1 : R) ^ (k * l) • (shuffle ν μ).domDomCongr (finCongr (Nat.add_comm l k)) := by
  ext v
  rw [shuffle_comm, AlternatingMap.smul_apply, AlternatingMap.domDomCongr_apply, smul_eq_mul]

section Uncurry

/-- `alternatizeUncurryFin` of `φ ⊗ Alt f` is the alternatization of `φ ⊠ f`. -/
theorem alternatizeUncurryFin_smulRight_alternatization (φ : M →ₗ[R] R)
    (f : MultilinearMap R (fun _ : Fin k => M) R) (v : Fin (k + 1) → M) :
    AlternatingMap.alternatizeUncurryFin (φ.smulRight (MultilinearMap.alternatization f)) v =
      MultilinearMap.alternatization (mulProd (MultilinearMap.ofSubsingleton R M R (0 : Fin 1) φ) f)
        (v ∘ finCongr (Nat.add_comm 1 k)) := by
  rw [← AlternatingMap.domDomCongr_apply, ← alternatization_domDomCongr,
    MultilinearMap.alternatization_apply, AlternatingMap.alternatizeUncurryFin_apply]
  have hH : ∀ w : Fin (k + 1) → M,
      ((mulProd (MultilinearMap.ofSubsingleton R M R (0 : Fin 1) φ) f).domDomCongr
        (finCongr (Nat.add_comm 1 k))) w = φ (w 0) * f (fun j => w j.succ) := by
    intro w
    simp only [MultilinearMap.domDomCongr_apply, mulProd_apply,
      MultilinearMap.ofSubsingleton_apply_apply]
    congr 2
    ext
    simp
  simp only [MultilinearMap.domDomCongr_apply, hH, LinearMap.smulRight_apply,
    AlternatingMap.smul_apply, MultilinearMap.alternatization_apply, Fin.removeNth_apply]
  cases k with
  | zero =>
    have h1 : ∀ x : Fin (0 + 1), x = 0 := fun x => Fin.ext (by have := x.isLt; omega)
    have h2 : ∀ σ : Perm (Fin (0 + 1)), σ = 1 := fun σ => Equiv.ext fun x => by
      rw [h1 (σ x), h1 x]; rfl
    rw [Fintype.sum_eq_single (0 : Fin (0 + 1)) (fun x hx => absurd (h1 x) hx),
      Fintype.sum_eq_single (1 : Perm (Fin (0 + 1))) (fun σ hσ => absurd (h2 σ) hσ)]
    simp only [Fin.val_zero, pow_zero, one_smul, Perm.sign_one, Perm.coe_one, id_eq,
      Fintype.sum_unique, Perm.default_eq, smul_eq_mul, Fin.succAbove_zero]
  | succ n =>
    rw [Fintype.sum_equiv Perm.decomposeFin' _ (fun p => Perm.sign (Perm.decomposeFin'.symm p) •
      (φ (v (Perm.decomposeFin'.symm p 0)) *
        f (fun j => v (Perm.decomposeFin'.symm p j.succ)))) (fun τ => by simp),
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Perm.decomposeFin'_symm, Perm.decomposeFin'Symm_zero, Perm.decomposeFin'Symm_succ,
      Perm.sign_decomposeFin'Symm, Finset.mul_sum, smul_eq_mul, Units.smul_def, Units.val_mul,
      Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, Int.cast_mul, Int.cast_pow,
      Int.cast_neg, Int.cast_one, zsmul_eq_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    ring

/-- `alternatizeUncurryFin` of `φ ⊗ θ` is the shuffle product of the `1`-form `φ` with `θ`. -/
theorem alternatizeUncurryFin_smulRight (φ : M →ₗ[R] R) (θ : M [⋀^Fin k]→ₗ[R] R)
    (v : Fin (k + 1) → M) :
    AlternatingMap.alternatizeUncurryFin (φ.smulRight θ) v =
      shuffle (AlternatingMap.ofSubsingleton R M R (0 : Fin 1) φ) θ
        (v ∘ finCongr (Nat.add_comm 1 k)) := by
  obtain ⟨f, hf⟩ := exists_alternatization_eq (θ.compLinearMap (tupleMap (R := R) v))
  have hL : AlternatingMap.alternatizeUncurryFin (φ.smulRight θ) v =
      AlternatingMap.alternatizeUncurryFin
        ((φ ∘ₗ tupleMap (R := R) v).smulRight (θ.compLinearMap (tupleMap (R := R) v)))
        (fun i => Pi.single i (1 : R)) := by
    simp only [AlternatingMap.alternatizeUncurryFin_apply, LinearMap.smulRight_apply,
      LinearMap.comp_apply, tupleMap_single, AlternatingMap.smul_apply,
      AlternatingMap.compLinearMap_apply, Fin.removeNth_apply]
    rfl
  rw [hL, ← compLinearMap_tupleMap_apply (R := R), ← shuffle_compLinearMap,
    ofSubsingleton_compLinearMap, ← hf, ← alternatization_ofSubsingleton, shuffle_alternatization,
    alternatizeUncurryFin_smulRight_alternatization]
  rfl

end Uncurry

end AlternatingAnalytic.Forms
