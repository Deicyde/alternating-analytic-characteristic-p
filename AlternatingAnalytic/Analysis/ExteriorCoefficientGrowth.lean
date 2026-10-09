import AlternatingAnalytic.Algebra.ExteriorBlocks
import AlternatingAnalytic.Analysis.EquivalentUltrametric
import AlternatingAnalytic.Analysis.ProjectiveExterior
import AlternatingAnalytic.Analysis.LaurentCoefficients

/-!
# Growth of disjoint block wedges

A coefficient map into the algebraic exterior power that recovers disjoint coordinate
wedges, with support dimension bounded by the norm, forces the partial sums of those
wedges to grow linearly. This excludes an equivalent ultrametric norm (Proposition E.1).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped BoundedContinuousFunction NNReal

namespace AlternatingAnalytic

variable {κ K F : Type*} [Field κ] [NormedField K]
  [NormedAddCommGroup F] [NormedSpace K F] [Module κ F]

/-- Recovering disjoint coordinate wedges through a coefficient map forces linear growth. -/
theorem exteriorCoefficient_block_growth {k : ℕ} (hk : 2 ≤ k)
    (η : F →ₗ[κ] ⋀[κ]^k (ℕ → κ)) (v : ℕ → F)
    (hv : ∀ j, η (v j) = exteriorPower.ιMulti κ k
      (fun i : Fin k => Pi.single (k * j + i.val + 1) (1 : κ)))
    {M : ℝ} (hM : 0 < M)
    (hbound : ∀ b, (exteriorSupportDim (η b) : ℝ) ≤ (k : ℝ) * M * ‖b‖)
    (N : ℕ) :
    (N : ℝ) / M ≤ ‖∑ i ∈ Finset.range N, v i‖ := by
  classical
  have hsum : η (∑ i ∈ Finset.range N, v i) =
      ∑ j : Fin N, exteriorPower.ιMulti κ k
        (fun i : Fin k => Pi.single (k * j.val + i.val + 1) (1 : κ)) := by
    simp only [map_sum, hv]
    exact (Fin.sum_univ_eq_sum_range _ N).symm
  have h := hbound (∑ i ∈ Finset.range N, v i)
  rw [hsum, exteriorSupportDim_consecutive_coordinate_blocks N k hk, Nat.cast_mul] at h
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  apply (div_le_iff₀ hM).mpr
  nlinarith

/-- A bounded exterior coefficient map that recovers disjoint coordinate wedges excludes
an equivalent ultrametric norm on `F`. -/
theorem not_hasEquivalentUltrametricNorm_of_exteriorCoefficient {k : ℕ} (hk : 2 ≤ k)
    (η : F →ₗ[κ] ⋀[κ]^k (ℕ → κ)) (v : ℕ → F)
    (hvnorm : ∀ j, ‖v j‖ ≤ 1)
    (hv : ∀ j, η (v j) = exteriorPower.ιMulti κ k
      (fun i : Fin k => Pi.single (k * j + i.val + 1) (1 : κ)))
    {M : ℝ} (hM : 0 < M)
    (hbound : ∀ b, (exteriorSupportDim (η b) : ℝ) ≤ (k : ℝ) * M * ‖b‖) :
    ¬ HasEquivalentUltrametricNorm K F :=
  not_hasEquivalentUltrametricNorm_of_linear_growth v hvnorm hM
    (exteriorCoefficient_block_growth hk η v hv hM hbound)

variable (κ : Type*) [Field κ] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] (k : ℕ)

/-- The wedge of the `j`-th block of `k` consecutive coordinates, in the completed
exterior power. -/
def laurentBlockWedge (j : ℕ) : ProjectiveExteriorCompletion (LaurentField κ r) ℕ k :=
  completedExteriorWedge (LaurentField κ r) ℕ k
    (fun i : Fin k => constantLaurentArray κ r
      (Pi.single (k * j + i.val + 1) (1 : κ)))

theorem norm_laurentBlockWedge_le_one (j : ℕ) : ‖laurentBlockWedge κ r k j‖ ≤ 1 := by
  unfold laurentBlockWedge
  calc
    _ ≤ ‖completedExteriorWedge (LaurentField κ r) ℕ k‖ *
        ∏ i : Fin k, ‖constantLaurentArray κ r
          (Pi.single (k * j + i.val + 1) (1 : κ))‖ :=
      (completedExteriorWedge (LaurentField κ r) ℕ k).le_opNorm _
    _ ≤ 1 * ∏ _i : Fin k, (1 : ℝ) := mul_le_mul
      (completedExteriorWedge_norm_le (LaurentField κ r) ℕ k)
      (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun _ _ =>
        norm_constantLaurentArray_le_one κ r _))
      (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) zero_le_one
    _ = 1 := by simp

end AlternatingAnalytic
