import AlternatingAnalytic.Algebra.ExteriorFlattening
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Support dimension of disjoint exterior blocks

For a biorthogonal family arranged in blocks of size at least two, coordinate
contractions recover every vector from the sum of the block wedges. Consequently
every supporting subspace contains the whole family, giving the exact support dimension.
-/

namespace AlternatingAnalytic

open Module

variable {L : Type*} [Field L]
  {V : Type*} [AddCommGroup V] [Module L V]

/-- Replacing one row of the identity matrix gives the corresponding entry as determinant. -/
theorem det_updateRow_one_eq {I : Type*} [Fintype I] [DecidableEq I]
    (α : I) (c : I → L) : (Matrix.updateRow (1 : Matrix I I L) α c).det = c α := by
  have hsum : ∑ i : I, c i • (1 : Matrix I I L) i = c := by
    ext j
    simp [Matrix.one_apply, Pi.smul_apply, smul_eq_mul]
  simpa only [hsum, Matrix.det_one, smul_eq_mul, mul_one] using
    Matrix.det_updateRow_sum (1 : Matrix I I L) α c

variable {B : Type*} {k : ℕ}

/-- The sum of wedges in a finite family of blocks. -/
noncomputable def exteriorBlockSum [Fintype B] (v : B × Fin k → V) : ⋀[L]^k V :=
  ∑ j : B, exteriorPower.ιMulti L k (fun i ↦ v (j, i))

/-- Contracting against the coordinates of one block recovers its selected vector
and kills every different block. The degree bound is needed for the latter assertion. -/
theorem exteriorContraction_block [DecidableEq B] (hk : 2 ≤ k)
    (v : B × Fin k → V) (ε : B × Fin k → Dual L V)
    (h₁ : ∀ p, ε p (v p) = 1) (h₀ : ∀ p q, p ≠ q → ε p (v q) = 0)
    (j l : B) (α : Fin k) :
    exteriorContraction α (fun i ↦ ε (j, i))
        (exteriorPower.ιMulti L k (fun i ↦ v (l, i))) =
      if j = l then v (l, α) else 0 := by
  classical
  have hpair (p q : B × Fin k) : ε p (v q) = if p = q then 1 else 0 := by
    split_ifs with h
    · subst q
      exact h₁ p
    · exact h₀ p q h
  apply (Module.Free.chooseBasis L V).eval_injective
  ext ψ
  change ψ _ = ψ _
  rw [exteriorContraction_eval, exteriorPower.alternatingMapToDual_apply_ιMulti]
  change (Matrix.of (fun a b ↦ Function.update (fun i ↦ ε (j, i)) α ψ a
    (v (l, b)))).transpose.det = _
  rw [Matrix.det_transpose]
  by_cases hjl : j = l
  · subst l
    have hmatrix : Matrix.of (fun a b ↦ Function.update (fun i ↦ ε (j, i)) α ψ a
        (v (j, b))) = Matrix.updateRow (1 : Matrix (Fin k) (Fin k) L) α
          (fun b ↦ ψ (v (j, b))) := by
      ext a b
      by_cases ha : a = α
      · subst a
        simp
      · simp [Matrix.updateRow_apply, ha, hpair, Matrix.one_apply]
    rw [hmatrix, det_updateRow_one_eq]
    simp
  · simp only [hjl, ↓reduceIte, map_zero]
    have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk
    obtain ⟨β, hβα⟩ := exists_ne α
    apply Matrix.det_eq_zero_of_row_eq_zero β
    intro i
    simp [Function.update_of_ne hβα, hpair, hjl]

/-- Coordinate contraction of the block sum recovers any chosen block vector. -/
theorem exteriorContraction_blockSum [Fintype B] (hk : 2 ≤ k)
    (v : B × Fin k → V) (ε : B × Fin k → Dual L V)
    (h₁ : ∀ p, ε p (v p) = 1) (h₀ : ∀ p q, p ≠ q → ε p (v q) = 0)
    (j : B) (α : Fin k) :
    exteriorContraction α (fun i ↦ ε (j, i)) (exteriorBlockSum v) = v (j, α) := by
  classical
  simp only [exteriorBlockSum, map_sum, exteriorContraction_block hk v ε h₁ h₀]
  simp

/-- Every support of a sum of disjoint biorthogonal blocks contains all block vectors. -/
theorem block_span_le_exterior_support [Fintype B] (hk : 2 ≤ k)
    (v : B × Fin k → V) (ε : B × Fin k → Dual L V)
    (h₁ : ∀ p, ε p (v p) = 1) (h₀ : ∀ p q, p ≠ q → ε p (v q) = 0)
    (U : Submodule L V) (hω : exteriorBlockSum v ∈ exteriorPowerSubmodule k U) :
    Submodule.span L (Set.range v) ≤ U := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨j, α⟩, rfl⟩
  rw [← exteriorContraction_blockSum hk v ε h₁ h₀ j α]
  exact exteriorContraction_mem_support α _ U hω

/-- The support dimension of a sum of `k`-fold disjoint biorthogonal blocks is exactly
the number of vectors in those blocks. -/
theorem exteriorSupportDim_blockSum [Fintype B] (hk : 2 ≤ k)
    (v : B × Fin k → V) (ε : B × Fin k → Dual L V)
    (h₁ : ∀ p, ε p (v p) = 1) (h₀ : ∀ p q, p ≠ q → ε p (v q) = 0) :
    exteriorSupportDim (exteriorBlockSum (L := L) v) = k * Fintype.card B := by
  let := FiniteDimensional.span_of_finite L (Set.finite_range v)
  have hv : LinearIndependent L v :=
    LinearIndependent.of_pairwise_dual_eq_zero_one v ε (fun p q h ↦ h₀ p q h) h₁
  have hdim : finrank L (Submodule.span L (Set.range v)) = k * Fintype.card B := by
    rw [finrank_span_eq_card hv, Fintype.card_prod, Fintype.card_fin, Nat.mul_comm]
  apply le_antisymm
  · rw [← hdim]
    apply exteriorSupportDim_le_finrank
    apply Submodule.sum_mem
    intro j hj
    exact ιMulti_mem_exteriorPowerSubmodule _ _
      (fun i ↦ Submodule.subset_span (Set.mem_range_self (j, i)))
  · obtain ⟨U, hU, hω, hUdim⟩ := exteriorSupportDim_attained (exteriorBlockSum (L := L) v)
    let := hU
    rw [← hdim, ← hUdim]
    exact Submodule.finrank_mono (block_span_le_exterior_support hk v ε h₁ h₀ U hω)

/-- In particular, disjoint blocks selected from any basis have the expected full support. -/
theorem exteriorSupportDim_basis_blocks {I : Type*} [Fintype B]
    (b : Basis I L V) (f : B × Fin k ↪ I) (hk : 2 ≤ k) :
    exteriorSupportDim (exteriorBlockSum (L := L) (b ∘ f)) = k * Fintype.card B := by
  classical
  apply exteriorSupportDim_blockSum hk (b ∘ f) (fun p ↦ b.coord (f p))
  · intro p
    simp
  · intro p q hpq
    simp [Module.Basis.coord_apply, f.injective.ne hpq]

/-- Disjoint coordinate-unit blocks in an arbitrary scalar function space have full support. -/
theorem exteriorSupportDim_coordinate_blocks {S : Type*} [DecidableEq S] [Fintype B]
    (f : B × Fin k ↪ S) (hk : 2 ≤ k) :
    exteriorSupportDim (exteriorBlockSum (L := L) (fun p ↦ (Pi.single (f p) (1 : L) : S → L))) =
      k * Fintype.card B := by
  classical
  apply exteriorSupportDim_blockSum hk _ (fun p ↦ LinearMap.proj (f p))
  · intro p
    simp
  · intro p q hpq
    simp [f.injective.ne hpq]

/-- The first `N` consecutive coordinate blocks used in the sequence-space construction
have support dimension exactly `k * N`. -/
theorem exteriorSupportDim_consecutive_coordinate_blocks (N k : ℕ) (hk : 2 ≤ k) :
    exteriorSupportDim (∑ j : Fin N, exteriorPower.ιMulti L k
      (fun i : Fin k ↦ (Pi.single (k * j.val + i.val + 1) (1 : L) : ℕ → L))) = k * N := by
  classical
  let f : Fin N × Fin k ↪ ℕ :=
    ⟨fun p ↦ k * p.1.val + p.2.val + 1, by
      intro p q h
      apply finProdFinEquiv.injective
      apply Fin.ext
      change p.2.val + k * p.1.val = q.2.val + k * q.1.val
      simpa only [Nat.add_comm] using Nat.add_right_cancel h⟩
  have hf (p : Fin N × Fin k) : f p = k * p.1.val + p.2.val + 1 := rfl
  simpa only [exteriorBlockSum, hf, Fintype.card_fin] using
    exteriorSupportDim_coordinate_blocks (L := L) f hk

end AlternatingAnalytic
