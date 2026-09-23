import AlternatingAnalytic.Algebra.FiniteFieldObstruction
import AlternatingAnalytic.Algebra.MultiplierObstruction
import AlternatingAnalytic.Algebra.Polarization

/-!
The normalized multiplier lift when the factorial is invertible.  The map is an
actual doubly multilinear map on all scalar sequences, with strongly alternating
vector slots.  Its support is contained in the span of the k² pairwise products.
-/

noncomputable section

open Finset Module

namespace AlternatingAnalytic

variable (L : Type*) [Field L] (k : ℕ)

/-- The unpermuted wedge of pointwise products, multilinear in both input groups. -/
def multiplierWedge : MultiplierMap L k (ℕ → L) :=
  (MultilinearMap.piLinearMap (exteriorPower.ιMulti L k).toMultilinearMap).compLinearMap
    fun _ => sequenceMultiplier L

@[simp]
theorem multiplierWedge_apply (u x : Fin k → ℕ → L) :
    multiplierWedge L k u x = exteriorPower.ιMulti L k (fun i n => u i n * x i n) := rfl

/-- The paper's normalized alternatization, with its literal permutation-sum formula. -/
def normalizedMultiplierLift : MultiplierMap L k (ℕ → L) :=
  (k.factorial : L)⁻¹ • ∑ σ : Equiv.Perm (Fin k), (multiplierWedge L k).domDomCongr σ

@[simp]
theorem normalizedMultiplierLift_apply (u x : Fin k → ℕ → L) :
    normalizedMultiplierLift L k u x = (k.factorial : L)⁻¹ •
      ∑ σ : Equiv.Perm (Fin k),
        exteriorPower.ιMulti L k (fun i n => u (σ i) n * x i n) := by
  simp only [normalizedMultiplierLift, _root_.smul_apply,
    _root_.sum_apply, MultilinearMap.domDomCongr_apply, multiplierWedge_apply]

/-- Permuting the multiplier slots is the usual signed alternatization of the vector slots. -/
theorem sum_multiplierWedge_eq_alternatization (u x : Fin k → ℕ → L) :
    (∑ σ : Equiv.Perm (Fin k),
      exteriorPower.ιMulti L k (fun i n => u (σ i) n * x i n)) =
      MultilinearMap.alternatization (multiplierWedge L k u) x := by
  rw [MultilinearMap.alternatization_apply]
  have hterm (σ : Equiv.Perm (Fin k)) :
      Equiv.Perm.sign σ • (multiplierWedge L k u).domDomCongr σ x =
        exteriorPower.ιMulti L k (fun i n => u (σ.symm i) n * x i n) := by
    have h := (exteriorPower.ιMulti L k).map_perm
      (fun i n => u i n * x (σ i) n) σ.symm
    simpa only [Equiv.Perm.sign_symm, Function.comp_def, Equiv.apply_symm_apply,
      MultilinearMap.domDomCongr_apply, multiplierWedge_apply] using h.symm
  simp_rw [hterm]
  exact (Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin k)))
    (fun σ => exteriorPower.ιMulti L k (fun i n => u (σ i) n * x i n))).symm

/-- Strong alternation holds over every field, including characteristic two. -/
theorem normalizedMultiplierLift_alternating (u x : Fin k → ℕ → L)
    {i j : Fin k} (hx : x i = x j) (hij : i ≠ j) :
    normalizedMultiplierLift L k u x = 0 := by
  rw [normalizedMultiplierLift_apply, sum_multiplierWedge_eq_alternatization,
    (MultilinearMap.alternatization (multiplierWedge L k u)).map_eq_zero_of_eq x hx hij,
    smul_zero]

/-- The vector-slot permutation formula follows from the actual alternating map. -/
theorem normalizedMultiplierLift_antisymmetric (u x : Fin k → ℕ → L)
    (σ : Equiv.Perm (Fin k)) :
    normalizedMultiplierLift L k u (x ∘ σ) =
      Equiv.Perm.sign σ • normalizedMultiplierLift L k u x := by
  simp only [normalizedMultiplierLift_apply, sum_multiplierWedge_eq_alternatization,
    AlternatingMap.map_perm]
  exact smul_comm _ _ _

/-- With invertible factorial, the pointwise diagonal is exactly the multiplier wedge. -/
theorem normalizedMultiplierLift_diagonal (hfactorial : (k.factorial : L) ≠ 0)
    (a : ℕ → L) (x : Fin k → ℕ → L) :
    normalizedMultiplierLift L k (fun _ => a) x =
      exteriorPower.ιMulti L k (fun i n => a n * x i n) := by
  rw [normalizedMultiplierLift_apply]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul L, smul_smul, inv_mul_cancel₀ hfactorial, one_smul]

/-- The normalized lift satisfies the genuine polarized multiplier-wedge identity. -/
theorem normalizedMultiplierLift_pol1 (hfactorial : (k.factorial : L) ≠ 0)
    (u x : Fin k → ℕ → L) :
    (∑ σ : Equiv.Perm (Fin k), normalizedMultiplierLift L k (u ∘ σ) x) =
      ∑ σ : Equiv.Perm (Fin k),
        exteriorPower.ιMulti L k (fun i n => u (σ i) n * x i n) := by
  have hd : ∀ a : ℕ → L,
      normalizedMultiplierLift L k (fun _ => a) = multiplierWedge L k (fun _ => a) := by
    intro a
    apply MultilinearMap.ext
    intro x
    exact normalizedMultiplierLift_diagonal L k hfactorial a x
  have h := MultilinearMap.sum_perm_eq_of_diagonal_eq
    (normalizedMultiplierLift L k) (multiplierWedge L k) hd u
  have hx := congrArg (fun M => M x) h
  simpa only [_root_.sum_apply, multiplierWedge_apply, Function.comp_def] using hx

/-- All summands lie in the span of the k² pairwise pointwise products. -/
theorem exteriorSupportDim_normalizedMultiplierLift_le (u x : Fin k → ℕ → L) :
    exteriorSupportDim (normalizedMultiplierLift L k u x) ≤ k ^ 2 := by
  classical
  rw [normalizedMultiplierLift_apply]
  apply (exteriorSupportDim_smul_le _ _).trans
  let s : Finset (ℕ → L) := Finset.univ.image
    (fun p : Fin k × Fin k => fun n => u p.1 n * x p.2 n)
  have hmem : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin k))), ∀ i,
      (fun n => u (σ i) n * x i n) ∈ s := by
    intro σ _ i
    exact Finset.mem_image.mpr ⟨(σ i, i), Finset.mem_univ _, rfl⟩
  calc
    exteriorSupportDim (∑ σ : Equiv.Perm (Fin k),
        exteriorPower.ιMulti L k (fun i n => u (σ i) n * x i n)) ≤
        finrank L (Submodule.span L (s : Set (ℕ → L))) :=
      exteriorSupportDim_sum_wedges_le s Finset.univ _ hmem
    _ ≤ s.card := finrank_span_finset_le_card s
    _ ≤ (Finset.univ : Finset (Fin k × Fin k)).card := Finset.card_image_le
    _ = k ^ 2 := by simp [pow_two]

/-- The normalized full-sequence lift restricted to the genuine finite cluster inputs. -/
def normalizedClusterLift : ClusterMap L k :=
  restrictClusterMap Finsupp.lcoeFun LinearMap.id (normalizedMultiplierLift L k)

@[simp]
theorem normalizedClusterLift_apply (u x : Fin k → ℕ →₀ L) :
    normalizedClusterLift L k u x =
      normalizedMultiplierLift L k (fun i n => u i n) (fun i n => x i n) := by
  rw [normalizedClusterLift, restrictClusterMap_apply, exteriorPower.map_id]
  rfl

theorem normalizedClusterLift_antisymmetric :
    ClusterVectorAntisymmetric (normalizedClusterLift L k) := by
  intro u x σ
  simpa only [normalizedClusterLift_apply, Function.comp_def] using
    normalizedMultiplierLift_antisymmetric L k (fun i n => u i n) (fun i n => x i n) σ

theorem normalizedClusterLift_pol1 (hfactorial : (k.factorial : L) ≠ 0) :
    ClusterPol1 (normalizedClusterLift L k) := by
  intro u x
  simpa only [normalizedClusterLift_apply, Function.comp_def] using
    normalizedMultiplierLift_pol1 L k hfactorial (fun i n => u i n) (fun i n => x i n)

/-- On every family of disjoint clusters, the actual determinant value is `1 / k!`. -/
theorem clusterValue_normalizedClusterLift (C : Fin k → Fin 4 → ℕ)
    (hinj : Function.Injective (fun t : Fin k × Fin 4 => C t.1 t.2)) :
    clusterValue (normalizedClusterLift L k) C = (k.factorial : L)⁻¹ := by
  classical
  simp only [clusterValue, normalizedClusterLift_apply, normalizedMultiplierLift_apply,
    map_smul, map_sum, Pi.smul_apply, Finset.sum_apply]
  have hsum : (∑ σ : Equiv.Perm (Fin k), determinantArray
      (exteriorPower.ιMulti L k (fun j n =>
        clusterInput clusterOperatorWeight (C (σ j)) n *
          clusterInput clusterVectorWeight (C j) n)) (fun j => C j 0)) = (1 : L) := by
    calc
      _ = ∑ σ : Equiv.Perm (Fin k), if σ = 1 then (1 : L) else 0 := by
        apply Finset.sum_congr rfl
        intro σ _
        exact cluster_multiplier_det_eq C hinj σ
      _ = 1 := by simp
  rw [hsum]
  simp

end AlternatingAnalytic
