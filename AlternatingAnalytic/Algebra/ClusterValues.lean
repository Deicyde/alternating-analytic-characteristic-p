import AlternatingAnalytic.Algebra.ClusterWeights
import AlternatingAnalytic.Algebra.DeterminantArray
import AlternatingAnalytic.Algebra.OrderPattern
import Mathlib.LinearAlgebra.Multilinear.Basic

/-!
# Coefficient expansions and cluster values

The coefficients and cluster values below come from an actual doubly multilinear map
into the exterior power of the space of sequences. An infinite set homogeneous for
the coefficient order patterns makes the cluster value depend only on the order of
the labeled blocks. This comparison needs separated increasing blocks; consecutiveness
is reserved for the subsequent cancellation argument.
-/

open Finset

namespace OrderPattern

/-- Order-pattern homogeneity with any finite coordinate index type. -/
theorem exists_infinite_order_homogeneous_finite {I C : Type*} [Fintype I] [Finite C]
    (T : (I → ℕ) → C) :
    ∃ H : Set ℕ, H.Infinite ∧ ∀ (z z' : I → ℕ),
      (∀ i, z i ∈ H) → (∀ i, z' i ∈ H) →
      (∀ i j, (z i < z j ↔ z' i < z' j) ∧ (z i = z j ↔ z' i = z' j)) →
      T z = T z' := by
  classical
  let e := Fintype.equivFin I
  obtain ⟨H, hH, hT⟩ := exists_infinite_order_homogeneous (Fintype.card I)
    (fun z => T (fun i => z (e i)))
  refine ⟨H, hH, fun z z' hz hz' hp => ?_⟩
  have h := hT (fun j => z (e.symm j)) (fun j => z' (e.symm j))
    (fun j => hz (e.symm j)) (fun j => hz' (e.symm j))
    (fun i j => hp (e.symm i) (e.symm j))
  simpa only [Equiv.symm_apply_apply] using h

end OrderPattern

namespace MultilinearMap

/-- Expand weighted finite sums independently in every input coordinate. -/
theorem map_weighted_sum {R A M I J : Type*} [CommSemiring R]
    [AddCommMonoid A] [Module R A] [AddCommMonoid M] [Module R M]
    [Fintype I] [DecidableEq I] [Fintype J] (P : MultilinearMap R (fun _ : I => A) M)
    (w : I → J → R) (v : I → J → A) :
    P (fun j => ∑ i, w j i • v j i) =
      ∑ a : I → J, (∏ j, w j (a j)) • P (fun j => v j (a j)) := by
  classical
  rw [P.map_sum]
  exact Finset.sum_congr rfl fun a _ => P.map_smul_univ _ _

end MultilinearMap

namespace AlternatingAnalytic

open Module

variable {L : Type*} [Field L] {k : ℕ}

/-- A doubly multilinear map on finitely supported scalar sequences. -/
abbrev ClusterMap (L : Type*) [Field L] (k : ℕ) :=
  MultilinearMap L (fun _ : Fin k => ℕ →₀ L)
    (MultilinearMap L (fun _ : Fin k => ℕ →₀ L) (⋀[L]^k (ℕ → L)))

/-- The coefficient obtained from unit inputs and coordinate determinant evaluation. -/
noncomputable def clusterCoefficient (Ψ : ClusterMap L k) (a y c : Fin k → ℕ) : L :=
  determinantArray (Ψ (fun j => Finsupp.single (a j) 1)
    (fun j => Finsupp.single (y j) 1)) c

/-- The three coordinate groups of a coefficient, for applying finite-index Ramsey. -/
noncomputable def clusterCoefficientTuple (Ψ : ClusterMap L k)
    (z : Fin 3 × Fin k → ℕ) : L :=
  clusterCoefficient Ψ (fun j => z (0, j)) (fun j => z (1, j)) (fun j => z (2, j))

/-- The actual unit-vector coefficients are order homogeneous on an infinite set. -/
theorem exists_infinite_clusterCoefficient_homogeneous [Finite L] (Ψ : ClusterMap L k) :
    ∃ H : Set ℕ, H.Infinite ∧ ∀ (z z' : Fin 3 × Fin k → ℕ),
      (∀ i, z i ∈ H) → (∀ i, z' i ∈ H) →
      (∀ i j, (z i < z j ↔ z' i < z' j) ∧ (z i = z j ↔ z' i = z' j)) →
      clusterCoefficientTuple Ψ z = clusterCoefficientTuple Ψ z' :=
  OrderPattern.exists_infinite_order_homogeneous_finite (clusterCoefficientTuple Ψ)

/-- A weighted vector supported on the four positions of a block. -/
noncomputable def clusterInput (w : Fin 4 → L) (C : Fin 4 → ℕ) : ℕ →₀ L :=
  ∑ i, w i • Finsupp.single (C i) 1

/-- The actual determinant evaluation on the cluster operator and vector inputs. -/
noncomputable def clusterValue (Ψ : ClusterMap L k) (C : Fin k → Fin 4 → ℕ) : L :=
  determinantArray (Ψ (fun j => clusterInput clusterOperatorWeight (C j))
    (fun j => clusterInput clusterVectorWeight (C j))) (fun j => C j 0)

/-- Expansion of an actual determinant evaluation on weighted unit-vector sums. -/
theorem determinantArray_weighted_expansion {I J : Type*} [Fintype I] [Fintype J]
    (Ψ : ClusterMap L k) (u : Fin k → I → L) (v : Fin k → J → L)
    (a : Fin k → I → ℕ) (y : Fin k → J → ℕ) (c : Fin k → ℕ) :
    determinantArray
      (Ψ (fun j => ∑ i, u j i • Finsupp.single (a j i) 1)
        (fun j => ∑ i, v j i • Finsupp.single (y j i) 1)) c =
      ∑ α : Fin k → I, ∑ β : Fin k → J,
        ((∏ j, u j (α j)) * (∏ j, v j (β j))) *
          clusterCoefficient Ψ (fun j => a j (α j)) (fun j => y j (β j)) c := by
  classical
  rw [Ψ.map_weighted_sum]
  simp only [_root_.sum_apply, smul_apply,
    MultilinearMap.map_weighted_sum, smul_sum, smul_smul, map_sum, map_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, clusterCoefficient]

/-- The coefficient expansion for arbitrary finitely supported inputs. The sums
range over the finite Cartesian products of their coordinate supports. -/
theorem determinantArray_support_expansion (Ψ : ClusterMap L k)
    (u v : Fin k → ℕ →₀ L) (c : Fin k → ℕ) :
    determinantArray (Ψ u v) c =
      ∑ a ∈ Fintype.piFinset (fun j => (u j).support),
        ∑ y ∈ Fintype.piFinset (fun j => (v j).support),
          ((∏ j, u j (a j)) * (∏ j, v j (y j))) * clusterCoefficient Ψ a y c := by
  classical
  have hu : u = fun j => ∑ i ∈ (u j).support, u j i • Finsupp.single i 1 := by
    funext j
    simpa only [Finsupp.smul_single_one, Finsupp.sum] using (u j).sum_single.symm
  have hv : v = fun j => ∑ i ∈ (v j).support, v j i • Finsupp.single i 1 := by
    funext j
    simpa only [Finsupp.smul_single_one, Finsupp.sum] using (v j).sum_single.symm
  conv_lhs => rw [hu, hv]
  rw [Ψ.map_sum_finset]
  simp only [_root_.sum_apply, smul_apply, MultilinearMap.map_smul_univ,
    MultilinearMap.map_sum_finset, smul_sum, smul_smul, map_sum, map_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, clusterCoefficient]

/-- The finite internal-position expansion of a cluster value. -/
theorem clusterValue_expansion (Ψ : ClusterMap L k) (C : Fin k → Fin 4 → ℕ) :
    clusterValue Ψ C = ∑ a : Fin k → Fin 4, ∑ y : Fin k → Fin 4,
      ((∏ j, clusterOperatorWeight (R := L) (a j)) *
        (∏ j, clusterVectorWeight (y j))) *
      clusterCoefficient Ψ (fun j => C j (a j)) (fun j => C j (y j))
        (fun j => C j 0) := by
  exact determinantArray_weighted_expansion Ψ (fun _ => clusterOperatorWeight)
    (fun _ => clusterVectorWeight) C C (fun j => C j 0)

/-- Increasing blocks with the same separation order have the same comparisons
between any two labeled internal positions. -/
theorem cluster_block_comparisons (C D : Fin k → Fin 4 → ℕ)
    (hC : ∀ j, StrictMono (C j)) (hD : ∀ j, StrictMono (D j))
    (τ : Equiv.Perm (Fin k))
    (hsepC : ∀ j l, τ j < τ l → ∀ p q, C j p < C l q)
    (hsepD : ∀ j l, τ j < τ l → ∀ p q, D j p < D l q)
    (j l : Fin k) (p q : Fin 4) :
    (C j p < C l q ↔ D j p < D l q) ∧ (C j p = C l q ↔ D j p = D l q) := by
  rcases lt_trichotomy (τ j) (τ l) with h | h | h
  · have hc := hsepC j l h p q
    have hd := hsepD j l h p q
    exact ⟨iff_of_true hc hd, iff_of_false (ne_of_lt hc) (ne_of_lt hd)⟩
  · have hjl := τ.injective h
    subst l
    exact ⟨(hC j).lt_iff_lt.trans (hD j).lt_iff_lt.symm,
      (hC j).injective.eq_iff.trans (hD j).injective.eq_iff.symm⟩
  · have hc := hsepC l j h q p
    have hd := hsepD l j h q p
    exact ⟨iff_of_false (not_lt_of_gt hc) (not_lt_of_gt hd),
      iff_of_false (ne_of_gt hc) (ne_of_gt hd)⟩

/-- Coefficient order homogeneity implies equality of the actual cluster values
for any two families having the same order of labeled blocks. -/
theorem clusterValue_eq_of_order (Ψ : ClusterMap L k) (H : Set ℕ)
    (hpattern : ∀ (z z' : Fin 3 × Fin k → ℕ),
      (∀ i, z i ∈ H) → (∀ i, z' i ∈ H) →
      (∀ i j, (z i < z j ↔ z' i < z' j) ∧ (z i = z j ↔ z' i = z' j)) →
      clusterCoefficientTuple Ψ z = clusterCoefficientTuple Ψ z')
    (C D : Fin k → Fin 4 → ℕ)
    (hC : ∀ j, StrictMono (C j)) (hD : ∀ j, StrictMono (D j))
    (hCH : ∀ j p, C j p ∈ H) (hDH : ∀ j p, D j p ∈ H)
    (τ : Equiv.Perm (Fin k))
    (hsepC : ∀ j l, τ j < τ l → ∀ p q, C j p < C l q)
    (hsepD : ∀ j l, τ j < τ l → ∀ p q, D j p < D l q) :
    clusterValue Ψ C = clusterValue Ψ D := by
  classical
  rw [clusterValue_expansion, clusterValue_expansion]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  let pos : Fin 3 → Fin k → Fin 4 := ![a, y, fun _ => 0]
  have h := hpattern (fun i => C i.2 (pos i.1 i.2))
    (fun i => D i.2 (pos i.1 i.2))
    (fun i => hCH i.2 (pos i.1 i.2)) (fun i => hDH i.2 (pos i.1 i.2))
    (fun i j => cluster_block_comparisons C D hC hD τ hsepC hsepD
      i.2 j.2 (pos i.1 i.2) (pos j.1 j.2))
  simpa [clusterCoefficientTuple, pos] using h

/-- Over a finite field there is an infinite set of indices on which the actual
cluster value depends only on the order of the labeled blocks. -/
theorem exists_infinite_clusterValue_order_invariant [Finite L] (Ψ : ClusterMap L k) :
    ∃ H : Set ℕ, H.Infinite ∧ ∀ (C D : Fin k → Fin 4 → ℕ),
      (∀ j, StrictMono (C j)) → (∀ j, StrictMono (D j)) →
      (∀ j p, C j p ∈ H) → (∀ j p, D j p ∈ H) →
      ∀ τ : Equiv.Perm (Fin k),
      (∀ j l, τ j < τ l → ∀ p q, C j p < C l q) →
      (∀ j l, τ j < τ l → ∀ p q, D j p < D l q) →
      clusterValue Ψ C = clusterValue Ψ D := by
  obtain ⟨H, hH, hpattern⟩ := exists_infinite_clusterCoefficient_homogeneous Ψ
  exact ⟨H, hH, fun C D hC hD hCH hDH τ hsepC hsepD =>
    clusterValue_eq_of_order Ψ H hpattern C D hC hD hCH hDH τ hsepC hsepD⟩

end AlternatingAnalytic
