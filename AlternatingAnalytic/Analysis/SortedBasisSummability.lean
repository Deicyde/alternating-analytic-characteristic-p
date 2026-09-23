import AlternatingAnalytic.Analysis.WeightedDeterminantBound
import Mathlib.Analysis.Normed.Module.Bases
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Order.Hom.PowersetCard
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

/-! Convergence of the actual sorted determinant family for an unconditional basis. -/

noncomputable section
open scoped BigOperators
open Filter Topology

namespace AlternatingAnalytic

/-- Products of finitely many independent null families tend to zero on the
cofinite filter of the entire tuple space, including degree zero. -/
theorem tendsto_fin_product_cofinite_zero {I : Type*} (n : ℕ)
    (a : Fin n → I → ℝ) (ha : ∀ j, Tendsto (a j) cofinite (𝓝 0)) :
    Tendsto (fun t : Fin n → I => ∏ j, a j (t j)) cofinite (𝓝 0) := by
  induction n with
  | zero => simp only [Filter.cofinite_eq_bot, tendsto_bot]
  | succ n ih =>
    have h := tendsto_mul_cofinite_nhds_zero (ha 0)
      (ih (fun j => a j.succ) (fun j => ha j.succ))
    have hc := h.comp (Fin.consEquiv (fun _ : Fin (n + 1) => I)).symm.injective.tendsto_cofinite
    simpa only [Function.comp_def, Fin.consEquiv_symm_apply, Fin.tail_def,
      Fin.prod_univ_succ] using hc

variable {K I E F : Type*} [NontriviallyNormedField K]
  [LinearOrder I] [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup F] [NormedSpace K F]

omit [LinearOrder I] in
/-- The norm-weighted coordinates of each basis expansion form a null family. -/
theorem tendsto_schauder_weighted_coord (b : UnconditionalSchauderBasis I K E) (x : E) :
    Tendsto (fun i => ‖b.coord i x‖ * ‖b i‖) cofinite (𝓝 0) := by
  simpa only [norm_smul, norm_zero] using (b.expansion x).summable.tendsto_cofinite_zero.norm

/-- The actual determinant term indexed by an increasing finite set of basis indices. -/
def sortedBasisTerm (b : UnconditionalSchauderBasis I K E) (n : ℕ)
    (g : E [×n]→L[K] F) (x : Fin n → E) (s : Set.powersetCard I n) : F :=
  let t := Set.powersetCard.ofFinEmbEquiv.symm s
  (Matrix.of fun i j => b.coord (t i) (x j)).det • g (b ∘ t)

/-- Permuting the increasing enumeration still gives an injective map from
finite subsets into the tuple space. -/
theorem sortedEnumeration_perm_injective (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Function.Injective (fun s : Set.powersetCard I n =>
      fun j => Set.powersetCard.ofFinEmbEquiv.symm s (σ j)) := by
  intro s t h
  apply Set.powersetCard.ofFinEmbEquiv.symm.injective
  ext j
  simpa only [Equiv.apply_symm_apply] using congrFun h (σ.symm j)

/-- Every weighted permutation product in the determinant is a null family. -/
theorem tendsto_sorted_weighted_product (b : UnconditionalSchauderBasis I K E) (n : ℕ)
    (x : Fin n → E) (σ : Equiv.Perm (Fin n)) :
    Tendsto (fun s : Set.powersetCard I n =>
      ∏ j, ‖b.coord (Set.powersetCard.ofFinEmbEquiv.symm s (σ j)) (x j)‖ *
        ‖b (Set.powersetCard.ofFinEmbEquiv.symm s (σ j))‖) cofinite (𝓝 0) :=
  (tendsto_fin_product_cofinite_zero n
    (fun j i => ‖b.coord i (x j)‖ * ‖b i‖)
    (fun j => tendsto_schauder_weighted_coord b (x j))).comp
      (sortedEnumeration_perm_injective (I := I) n σ).tendsto_cofinite

/-- The determinant family is bounded by the finite sum of its weighted permutation products. -/
theorem norm_sortedBasisTerm_le (b : UnconditionalSchauderBasis I K E) (n : ℕ)
    (g : E [×n]→L[K] F) (x : Fin n → E) (s : Set.powersetCard I n) :
    ‖sortedBasisTerm b n g x s‖ ≤ ‖g‖ *
      ∑ σ : Equiv.Perm (Fin n), ∏ j,
        ‖b.coord (Set.powersetCard.ofFinEmbEquiv.symm s (σ j)) (x j)‖ *
        ‖b (Set.powersetCard.ofFinEmbEquiv.symm s (σ j))‖ := by
  classical
  let t := Set.powersetCard.ofFinEmbEquiv.symm s
  let a : Matrix (Fin n) (Fin n) K := fun i j => b.coord (t i) (x j)
  have hdet : ‖a.det‖ ≤ ∑ σ : Equiv.Perm (Fin n), ∏ j, ‖a (σ j) j‖ := by
    rw [Matrix.det_apply]
    simpa only [norm_units_zsmul, norm_prod] using
      (norm_sum_le Finset.univ (fun σ : Equiv.Perm (Fin n) =>
        Equiv.Perm.sign σ • ∏ j, a (σ j) j))
  change ‖a.det • g (b ∘ t)‖ ≤ _
  rw [norm_smul]
  calc
    _ ≤ (∑ σ : Equiv.Perm (Fin n), ∏ j, ‖a (σ j) j‖) *
        (‖g‖ * ∏ j, ‖b (t j)‖) :=
      mul_le_mul hdet (g.le_opNorm _) (norm_nonneg _)
        (Finset.sum_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => norm_nonneg _)
    _ = ‖g‖ * ∑ σ : Equiv.Perm (Fin n),
        ∏ j, ‖a (σ j) j‖ * ‖b (t (σ j))‖ := by
      rw [mul_left_comm, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro σ _
      rw [Finset.prod_mul_distrib]
      exact congrArg (fun z : ℝ => (∏ j, ‖a (σ j) j‖) * z)
        (Equiv.prod_comp σ (fun j => ‖b (t j)‖)).symm
    _ = _ := rfl

/-- The actual sorted determinant terms tend to zero without countability or
completeness of the space carrying the basis. -/
theorem tendsto_sortedBasisTerm (b : UnconditionalSchauderBasis I K E) (n : ℕ)
    (g : E [×n]→L[K] F) (x : Fin n → E) :
    Tendsto (sortedBasisTerm b n g x) cofinite (𝓝 0) := by
  classical
  apply squeeze_zero_norm (fun s => norm_sortedBasisTerm_le b n g x s)
  have h := tendsto_finsetSum Finset.univ (fun σ _ => tendsto_sorted_weighted_product b n x σ)
  simpa only [Finset.sum_const_zero, mul_zero] using h.const_mul ‖g‖

/-- Over a complete ultrametric target the sorted determinant family is summable. -/
theorem summable_sortedBasisTerm [IsUltrametricDist F] [CompleteSpace F]
    (b : UnconditionalSchauderBasis I K E) (n : ℕ)
    (g : E [×n]→L[K] F) (x : Fin n → E) :
    Summable (sortedBasisTerm b n g x) :=
  (NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero _).mpr
    (tendsto_sortedBasisTerm b n g x)

end AlternatingAnalytic
