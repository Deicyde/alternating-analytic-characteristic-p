import Mathlib.LinearAlgebra.Alternating.DomCoprod
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
import Mathlib.GroupTheory.Perm.Fin

/-!
# The shuffle product of scalar alternating maps

For a commutative ring `R` and an `R`-module `M`, `shuffle μ ν` is the product of
`μ ∈ Alt^k(M; R)` and `ν ∈ Alt^l(M; R)` given by Mathlib's `AlternatingMap.domCoprod` (a signed sum
over shuffles), followed by multiplication `R ⊗ R → R` and reindexing along `finSumFinEquiv`.
On multilinear maps, `mulProd a b` is the unsymmetrized product `v ↦ a(v_{<k}) b(v_{≥k})`.
The main result of this file, `shuffle_alternatization`, says that the shuffle product of two
alternatizations is the alternatization of the product; it is Mathlib's
`MultilinearMap.domCoprod_alternization`, transported along `mul'` and `finSumFinEquiv`. We also
prove the associativity, commutativity and unit laws of `mulProd`, the bilinearity of `shuffle`,
and its naturality under linear maps and under reindexing by `finCongr`.
-/

open Equiv

namespace AlternatingAnalytic.Forms

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The shuffle product of two scalar alternating maps. -/
noncomputable def shuffle {k l : ℕ} (μ : M [⋀^Fin k]→ₗ[R] R) (ν : M [⋀^Fin l]→ₗ[R] R) :
    M [⋀^Fin (k + l)]→ₗ[R] R :=
  ((LinearMap.mul' R R).compAlternatingMap (μ.domCoprod ν)).domDomCongr finSumFinEquiv

/-- The unsymmetrized product `v ↦ a(v_{<k}) b(v_{≥k})` of two scalar multilinear maps. -/
noncomputable def mulProd {k l : ℕ} (a : MultilinearMap R (fun _ : Fin k => M) R)
    (b : MultilinearMap R (fun _ : Fin l => M) R) : MultilinearMap R (fun _ : Fin (k + l) => M) R :=
  ((LinearMap.mul' R R).compMultilinearMap (a.domCoprod b)).domDomCongr finSumFinEquiv

variable {k l m : ℕ}

/-- The value of `mulProd`. -/
theorem mulProd_apply (a : MultilinearMap R (fun _ : Fin k => M) R)
    (b : MultilinearMap R (fun _ : Fin l => M) R) (v : Fin (k + l) → M) :
    mulProd a b v = a (fun i => v (Fin.castAdd l i)) * b (fun j => v (Fin.natAdd k j)) := by
  simp [mulProd, MultilinearMap.domCoprod_apply]

/-- Alternatization commutes with reindexing. -/
theorem alternatization_domDomCongr {N : Type*} [AddCommGroup N] [Module R N]
    {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] (e : ι ≃ ι')
    (a : MultilinearMap R (fun _ : ι => M) N) :
    MultilinearMap.alternatization (a.domDomCongr e) =
      (MultilinearMap.alternatization a).domDomCongr e := by
  ext v
  simp only [MultilinearMap.alternatization_apply, AlternatingMap.domDomCongr_apply,
    MultilinearMap.domDomCongr_apply, Function.comp_apply]
  refine Fintype.sum_equiv (e.symm.permCongr) _ _ fun σ => ?_
  simp [Perm.sign_permCongr]

/-- The shuffle product of two alternatizations is the alternatization of their product. -/
theorem shuffle_alternatization (a : MultilinearMap R (fun _ : Fin k => M) R)
    (b : MultilinearMap R (fun _ : Fin l => M) R) :
    shuffle (MultilinearMap.alternatization a) (MultilinearMap.alternatization b) =
      MultilinearMap.alternatization (mulProd a b) := by
  rw [mulProd, alternatization_domDomCongr, LinearMap.compMultilinearMap_alternatization,
    MultilinearMap.domCoprod_alternization]
  rfl

/-- The product of multilinear maps is associative up to reindexing. -/
theorem mulProd_assoc (a : MultilinearMap R (fun _ : Fin k => M) R)
    (b : MultilinearMap R (fun _ : Fin l => M) R) (c : MultilinearMap R (fun _ : Fin m => M) R) :
    mulProd (mulProd a b) c =
      (mulProd a (mulProd b c)).domDomCongr (finCongr (Nat.add_assoc k l m).symm) := by
  ext v
  simp only [mulProd_apply, MultilinearMap.domDomCongr_apply, mul_assoc]
  congr 2
  congr 1
  funext i
  congr 1
  ext
  simp only [finCongr_apply, Fin.val_cast, Fin.val_natAdd]
  omega

/-- Swapping the factors of `mulProd` reindexes it by `finAddFlip`. -/
theorem mulProd_comm (a : MultilinearMap R (fun _ : Fin k => M) R)
    (b : MultilinearMap R (fun _ : Fin l => M) R) :
    mulProd b a = (mulProd a b).domDomCongr finAddFlip := by
  ext v
  rw [MultilinearMap.domDomCongr_apply, mulProd_apply, mulProd_apply, mul_comm]
  congr 2
  · funext i
    exact congrArg v (finAddFlip_apply_castAdd i l).symm
  · funext j
    exact congrArg v (finAddFlip_apply_natAdd j k).symm

/-- The constant `1` is a left unit for `mulProd` up to reindexing. -/
theorem constOfIsEmpty_mulProd (a : MultilinearMap R (fun _ : Fin k => M) R) :
    mulProd (MultilinearMap.constOfIsEmpty R (fun _ : Fin 0 => M) (1 : R)) a =
      a.domDomCongr (finCongr (Nat.zero_add k).symm) := by
  ext v
  simp only [mulProd_apply, MultilinearMap.constOfIsEmpty_apply, Function.const_apply, one_mul,
    MultilinearMap.domDomCongr_apply]
  congr 1
  funext j
  congr 1
  ext
  simp

/-- The constant `1` is a right unit for `mulProd` up to reindexing. -/
theorem mulProd_constOfIsEmpty (a : MultilinearMap R (fun _ : Fin k => M) R) :
    mulProd a (MultilinearMap.constOfIsEmpty R (fun _ : Fin 0 => M) (1 : R)) =
      a.domDomCongr (finCongr (Nat.add_zero k).symm) := by
  ext v
  simp only [mulProd_apply, MultilinearMap.constOfIsEmpty_apply, Function.const_apply, mul_one,
    MultilinearMap.domDomCongr_apply]
  rfl

/-- The alternatization of the constant `0`-ary map `1` is `1`. -/
theorem alternatization_constOfIsEmpty :
    MultilinearMap.alternatization (MultilinearMap.constOfIsEmpty R (fun _ : Fin 0 => M) (1 : R)) =
      AlternatingMap.constOfIsEmpty R M (Fin 0) (1 : R) := by
  ext v
  simp [MultilinearMap.alternatization_apply]

section Bilinear

/-- The shuffle product is additive in the first factor. -/
theorem shuffle_add_left (μ₁ μ₂ : M [⋀^Fin k]→ₗ[R] R) (ν : M [⋀^Fin l]→ₗ[R] R) :
    shuffle (μ₁ + μ₂) ν = shuffle μ₁ ν + shuffle μ₂ ν := by
  ext v
  simp [shuffle, ← AlternatingMap.domCoprod'_apply, TensorProduct.add_tmul]

/-- The shuffle product is additive in the second factor. -/
theorem shuffle_add_right (μ : M [⋀^Fin k]→ₗ[R] R) (ν₁ ν₂ : M [⋀^Fin l]→ₗ[R] R) :
    shuffle μ (ν₁ + ν₂) = shuffle μ ν₁ + shuffle μ ν₂ := by
  ext v
  simp [shuffle, ← AlternatingMap.domCoprod'_apply, TensorProduct.tmul_add]

/-- The shuffle product is homogeneous in the first factor. -/
theorem shuffle_smul_left (c : R) (μ : M [⋀^Fin k]→ₗ[R] R) (ν : M [⋀^Fin l]→ₗ[R] R) :
    shuffle (c • μ) ν = c • shuffle μ ν := by
  ext v
  simp [shuffle, ← AlternatingMap.domCoprod'_apply, ← TensorProduct.smul_tmul']

/-- The shuffle product is homogeneous in the second factor. -/
theorem shuffle_smul_right (c : R) (μ : M [⋀^Fin k]→ₗ[R] R) (ν : M [⋀^Fin l]→ₗ[R] R) :
    shuffle μ (c • ν) = c • shuffle μ ν := by
  ext v
  simp [shuffle, ← AlternatingMap.domCoprod'_apply, TensorProduct.tmul_smul]

/-- The shuffle product commutes with finite sums in the first factor. -/
theorem shuffle_sum_left {ι : Type*} (s : Finset ι) (μ : ι → M [⋀^Fin k]→ₗ[R] R)
    (ν : M [⋀^Fin l]→ₗ[R] R) : shuffle (∑ i ∈ s, μ i) ν = ∑ i ∈ s, shuffle (μ i) ν := by
  classical
  induction s using Finset.induction_on with
  | empty => ext v; simp [shuffle, ← AlternatingMap.domCoprod'_apply]
  | insert i s hi ih => rw [Finset.sum_insert hi, shuffle_add_left, ih, Finset.sum_insert hi]

/-- The shuffle product commutes with finite sums in the second factor. -/
theorem shuffle_sum_right {ι : Type*} (s : Finset ι) (μ : M [⋀^Fin k]→ₗ[R] R)
    (ν : ι → M [⋀^Fin l]→ₗ[R] R) : shuffle μ (∑ i ∈ s, ν i) = ∑ i ∈ s, shuffle μ (ν i) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext v; simp [shuffle, ← AlternatingMap.domCoprod'_apply]
  | insert i s hi ih => rw [Finset.sum_insert hi, shuffle_add_right, ih, Finset.sum_insert hi]

end Bilinear

section Naturality

variable {M' : Type*} [AddCommGroup M'] [Module R M']

/-- `AlternatingMap.domCoprod` commutes with pullback along linear maps. -/
theorem domCoprod_compLinearMap {ιa ιb : Type*} [Fintype ιa] [Fintype ιb] [DecidableEq ιa]
    [DecidableEq ιb] (μ : M [⋀^ιa]→ₗ[R] R) (ν : M [⋀^ιb]→ₗ[R] R) (g : M' →ₗ[R] M) :
    (μ.compLinearMap g).domCoprod (ν.compLinearMap g) = (μ.domCoprod ν).compLinearMap g := by
  ext v
  simp only [AlternatingMap.domCoprod_apply, AlternatingMap.compLinearMap_apply, sum_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  induction σ using Quotient.inductionOn' with
  | h σ => simp [AlternatingMap.domCoprod.summand_mk'', MultilinearMap.domCoprod_apply]

/-- The shuffle product commutes with pullback along linear maps. -/
theorem shuffle_compLinearMap (μ : M [⋀^Fin k]→ₗ[R] R) (ν : M [⋀^Fin l]→ₗ[R] R)
    (g : M' →ₗ[R] M) :
    shuffle (μ.compLinearMap g) (ν.compLinearMap g) = (shuffle μ ν).compLinearMap g := by
  ext v
  simp only [shuffle, domCoprod_compLinearMap]
  rfl

end Naturality

/-- The shuffle product commutes with reindexing the first factor along `finCongr`. -/
theorem shuffle_domDomCongr_finCongr_left {k k' : ℕ} (h : k = k') (μ : M [⋀^Fin k]→ₗ[R] R)
    (ν : M [⋀^Fin l]→ₗ[R] R) (v : Fin (k' + l) → M) :
    shuffle (μ.domDomCongr (finCongr h)) ν v = shuffle μ ν (v ∘ finCongr (by omega)) := by
  subst h
  congr 1

/-- The shuffle product commutes with reindexing the second factor along `finCongr`. -/
theorem shuffle_domDomCongr_finCongr_right {l l' : ℕ} (h : l = l') (μ : M [⋀^Fin k]→ₗ[R] R)
    (ν : M [⋀^Fin l]→ₗ[R] R) (v : Fin (k + l') → M) :
    shuffle μ (ν.domDomCongr (finCongr h)) v = shuffle μ ν (v ∘ finCongr (by omega)) := by
  subst h
  congr 1

end AlternatingAnalytic.Forms
