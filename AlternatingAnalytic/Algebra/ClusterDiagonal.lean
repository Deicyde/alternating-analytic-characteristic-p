import AlternatingAnalytic.Algebra.ClusterValues

/-!
# The polarized diagonal sum of cluster values

The genuine multiplier-wedge identity and vector-slot antisymmetry give a sum of
actual cluster values equal to one. The determinant calculation is valid in every
characteristic; no vanishing on repeated vector inputs is assumed.
-/

open Finset Module

namespace AlternatingAnalytic

variable {L : Type*} [Field L] {k : ℕ}

/-- Antisymmetry in the vector slots, stated by the permutation sign. This does
not impose the additional equal-input vanishing condition of an alternating map. -/
def ClusterVectorAntisymmetric (Ψ : ClusterMap L k) : Prop :=
  ∀ (u v : Fin k → ℕ →₀ L) (σ : Equiv.Perm (Fin k)),
    Ψ u (v ∘ σ) = Equiv.Perm.sign σ • Ψ u v

/-- The multilinear polarized identity for actual pointwise sequence multipliers. -/
def ClusterPol1 (Ψ : ClusterMap L k) : Prop :=
  ∀ (u v : Fin k → ℕ →₀ L),
    (∑ σ : Equiv.Perm (Fin k), Ψ (u ∘ σ) v) =
      ∑ σ : Equiv.Perm (Fin k),
        exteriorPower.ιMulti L k (fun j n => u (σ j) n * v j n)

/-- Permuting the output coordinates of a determinant array introduces the sign. -/
theorem determinantArray_perm (ω : ⋀[L]^k (ℕ → L)) (c : Fin k → ℕ)
    (σ : Equiv.Perm (Fin k)) :
    determinantArray ω (c ∘ σ) = Equiv.Perm.sign σ • determinantArray ω c :=
  exteriorEvaluationArray_perm (L := L) (V := ℕ → L) (S := ℕ) (k := k)
    (fun n : ℕ => (LinearMap.proj n : (ℕ → L) →ₗ[L] L)) ω c σ

/-- Integer-unit scalar multiplication commutes with determinant evaluation. -/
theorem determinantArray_units_smul (s : ℤˣ) (ω : ⋀[L]^k (ℕ → L)) (c : Fin k → ℕ) :
    determinantArray (s • ω) c = s • determinantArray ω c := by
  simp only [Units.smul_def, map_zsmul, Pi.smul_apply]

/-- The vector-permutation sign and the output-coordinate sign cancel. -/
theorem determinantArray_perm_cancel (Ψ : ClusterMap L k)
    (hanti : ClusterVectorAntisymmetric Ψ) (u v : Fin k → ℕ →₀ L)
    (c : Fin k → ℕ) (σ : Equiv.Perm (Fin k)) :
    determinantArray (Ψ (u ∘ σ) v) c =
      determinantArray (Ψ (u ∘ σ) (v ∘ σ)) (c ∘ σ) := by
  symm
  rw [determinantArray_perm, hanti, determinantArray_units_smul,
    smul_smul, Int.units_mul_self, one_smul]

/-- A weighted block vector evaluated at a coordinate of a disjoint block. -/
theorem clusterInput_at_block_coordinate {I : Type*} [DecidableEq I]
    (C : I → Fin 4 → ℕ)
    (hinj : Function.Injective (fun t : I × Fin 4 => C t.1 t.2))
    (w : Fin 4 → L) (j i : I) (q : Fin 4) :
    clusterInput w (C j) (C i q) = if j = i then w q else 0 := by
  classical
  simp only [clusterInput, Finsupp.finsetSum_apply]
  by_cases hji : j = i
  · subst i
    simp only [ite_true]
    rw [Finset.sum_eq_single q]
    · simp
    · intro p _ hpq
      have hne : C j p ≠ C j q := by
        intro h
        have hp : (j, p) = (j, q) := hinj h
        exact hpq (congrArg Prod.snd hp)
      simp [hne]
    · simp
  · rw [ite_eq_right hji]
    apply Finset.sum_eq_zero
    intro p _
    have hne : C j p ≠ C i q := by
      intro h
      have hp : (j, p) = (i, q) := hinj h
      exact hji (congrArg Prod.fst hp)
    simp [hne]

/-- Only the identity operator assignment contributes to the polarized wedge sum
on disjoint clusters, and its determinant is one. -/
theorem cluster_multiplier_det_eq (C : Fin k → Fin 4 → ℕ)
    (hinj : Function.Injective (fun t : Fin k × Fin 4 => C t.1 t.2))
    (σ : Equiv.Perm (Fin k)) :
    determinantArray (exteriorPower.ιMulti L k (fun j n =>
      clusterInput clusterOperatorWeight (C (σ j)) n *
        clusterInput clusterVectorWeight (C j) n)) (fun j => C j 0) =
      if σ = 1 then 1 else 0 := by
  classical
  rw [determinantArray_ιMulti]
  by_cases hσ : σ = 1
  · subst σ
    simp only [ite_true]
    have hM : (fun i j : Fin k =>
        clusterInput (clusterOperatorWeight (R := L)) (C j) (C i 0) *
          clusterInput clusterVectorWeight (C j) (C i 0)) = (1 : Matrix (Fin k) (Fin k) L) := by
      ext i j
      rw [clusterInput_at_block_coordinate C hinj,
        clusterInput_at_block_coordinate C hinj]
      simp [clusterOperatorWeight, clusterVectorWeight, Matrix.one_apply, eq_comm]
    simpa only [Equiv.Perm.one_apply, Matrix.det_one] using congrArg Matrix.det hM
  · rw [ite_eq_right hσ]
    have hmoved : ∃ j, σ j ≠ j := by
      by_contra! h
      exact hσ (Equiv.ext h)
    obtain ⟨j, hj⟩ := hmoved
    apply Matrix.det_eq_zero_of_column_eq_zero j
    intro i
    rw [clusterInput_at_block_coordinate C hinj,
      clusterInput_at_block_coordinate C hinj]
    by_cases hji : j = i
    · subst i
      simp [hj]
    · simp [hji]

/-- The polarized multiplier identity gives the sum of the actual permuted cluster
values. This needs only disjoint block coordinates, without homogeneity or a bound. -/
theorem sum_clusterValue_perm_eq_one (Ψ : ClusterMap L k)
    (hanti : ClusterVectorAntisymmetric Ψ) (hpol : ClusterPol1 Ψ)
    (C : Fin k → Fin 4 → ℕ)
    (hinj : Function.Injective (fun t : Fin k × Fin 4 => C t.1 t.2)) :
    (∑ σ : Equiv.Perm (Fin k), clusterValue Ψ (fun j => C (σ j))) = 1 := by
  classical
  let u : Fin k → ℕ →₀ L := fun j => clusterInput clusterOperatorWeight (C j)
  let v : Fin k → ℕ →₀ L := fun j => clusterInput clusterVectorWeight (C j)
  let c : Fin k → ℕ := fun j => C j 0
  calc
    _ = ∑ σ : Equiv.Perm (Fin k), determinantArray (Ψ (u ∘ σ) v) c := by
      apply Finset.sum_congr rfl
      intro σ _
      exact (determinantArray_perm_cancel Ψ hanti u v c σ).symm
    _ = ∑ σ : Equiv.Perm (Fin k), determinantArray
        (exteriorPower.ιMulti L k (fun j n => u (σ j) n * v j n)) c := by
      have h := congrArg (fun ω => determinantArray ω c) (hpol u v)
      simpa only [map_sum, Finset.sum_apply] using h
    _ = ∑ σ : Equiv.Perm (Fin k), if σ = 1 then (1 : L) else 0 := by
      apply Finset.sum_congr rfl
      intro σ _
      exact cluster_multiplier_det_eq C hinj σ
    _ = 1 := by simp

/-- Strictly increasing separated blocks have distinct labeled coordinates. -/
theorem cluster_coordinates_injective_of_separated (C : Fin k → Fin 4 → ℕ)
    (hmono : ∀ j, StrictMono (C j))
    (hsep : ∀ j l, j ≠ l → (∀ p q, C j p < C l q) ∨ (∀ p q, C l p < C j q)) :
    Function.Injective (fun t : Fin k × Fin 4 => C t.1 t.2) := by
  rintro ⟨j, p⟩ ⟨l, q⟩ h
  by_cases hjl : j = l
  · subst l
    have hp : p = q := (hmono j).injective h
    subst q
    rfl
  · rcases hsep j l hjl with hlt | hgt
    · exact ((ne_of_lt (hlt p q)) h).elim
    · exact ((ne_of_gt (hgt q p)) h).elim

/-- The actual permutation sum for increasing pairwise separated clusters. -/
theorem sum_clusterValue_perm_eq_one_of_separated (Ψ : ClusterMap L k)
    (hanti : ClusterVectorAntisymmetric Ψ) (hpol : ClusterPol1 Ψ)
    (C : Fin k → Fin 4 → ℕ) (hmono : ∀ j, StrictMono (C j))
    (hsep : ∀ j l, j ≠ l → (∀ p q, C j p < C l q) ∨ (∀ p q, C l p < C j q)) :
    (∑ σ : Equiv.Perm (Fin k), clusterValue Ψ (fun j => C (σ j))) = 1 :=
  sum_clusterValue_perm_eq_one Ψ hanti hpol C
    (cluster_coordinates_injective_of_separated C hmono hsep)

/-- On a coefficient-homogeneous set the diagonal identity also holds for any
actual representative of each permutation order. This is the paper's sum of χ(τ). -/
theorem sum_clusterValue_order_eq_one (Ψ : ClusterMap L k)
    (hanti : ClusterVectorAntisymmetric Ψ) (hpol : ClusterPol1 Ψ)
    (H : Set ℕ)
    (hpattern : ∀ (z z' : Fin 3 × Fin k → ℕ),
      (∀ i, z i ∈ H) → (∀ i, z' i ∈ H) →
      (∀ i j, (z i < z j ↔ z' i < z' j) ∧ (z i = z j ↔ z' i = z' j)) →
      clusterCoefficientTuple Ψ z = clusterCoefficientTuple Ψ z')
    (C : Fin k → Fin 4 → ℕ) (hmono : ∀ j, StrictMono (C j))
    (hCH : ∀ j p, C j p ∈ H)
    (horder : ∀ j l, j < l → ∀ p q, C j p < C l q)
    (R : Equiv.Perm (Fin k) → Fin k → Fin 4 → ℕ)
    (hRmono : ∀ σ j, StrictMono (R σ j)) (hRH : ∀ σ j p, R σ j p ∈ H)
    (hRorder : ∀ σ j l, σ j < σ l → ∀ p q, R σ j p < R σ l q) :
    (∑ σ : Equiv.Perm (Fin k), clusterValue Ψ (R σ)) = 1 := by
  classical
  calc
    _ = ∑ σ : Equiv.Perm (Fin k), clusterValue Ψ (fun j => C (σ j)) := by
      apply Finset.sum_congr rfl
      intro σ _
      exact clusterValue_eq_of_order Ψ H hpattern (R σ) (fun j => C (σ j))
        (hRmono σ) (fun j => hmono (σ j)) (hRH σ) (fun j p => hCH (σ j) p)
        σ (hRorder σ) (fun j l h p q => horder (σ j) (σ l) h p q)
    _ = 1 := by
      apply sum_clusterValue_perm_eq_one_of_separated Ψ hanti hpol C hmono
      intro j l hjl
      rcases lt_or_gt_of_ne hjl with h | h
      · exact Or.inl (horder j l h)
      · exact Or.inr (horder l j h)

end AlternatingAnalytic
