import AlternatingAnalytic.Analysis.DenseScalarFamilyExtension
import AlternatingAnalytic.Analysis.BaseChangeAlternatingCriterion
import Mathlib.LinearAlgebra.Determinant

/-!
# Top-degree coefficients on dense normed sources

The target submodule need not be complete. Extension takes place only after its
isometric inclusion into the complete scalar field.
-/

noncomputable section
open scoped BigOperators

namespace AlternatingAnalytic

variable {K L E H I : Type*}
  [NontriviallyNormedField K] [NontriviallyNormedField L] [NormedAlgebra K L]
  [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup H] [NormedSpace K H] [NormedSpace L H]
  [IsScalarTower K L H] [CompleteSpace L] [Fintype I] [DecidableEq I]

/-- Coefficients whose determinant form takes values in the original target. -/
def determinantCoefficientSubmodule (j : E →ₗ[K] H) (b : Module.Basis I L H)
    (G : Submodule K L) : Submodule K L where
  carrier := {c | ∀ x : I → E, c * b.det (fun i => j (x i)) ∈ G}
  zero_mem' := by simp
  add_mem' hc hd x := by simpa only [add_mul] using G.add_mem (hc x) (hd x)
  smul_mem' k c hc x := by
    simpa only [smul_mul_assoc] using G.smul_mem k (hc x)

variable (hKL : DenseRange (algebraMap K L))
  (j : E →ₗᵢ[K] H) (hj : DenseRange j) (b : Module.Basis I L H)
  (G : Submodule K L) (s : I → E) (hs : ∀ i, j (s i) = b i)

/-- Extend an already alternating map into the complete field, preserving strong alternation. -/
def denseAlternatingScalarExtension (m : E [⋀^I]→L[K] G) : H [⋀^I]→L[L] L :=
  let q := denseScalarFamilyExtension hKL (fun _ : I => j) (fun _ => hj)
    (G.subtypeL.compContinuousMultilinearMap m.toContinuousMultilinearMap)
  { q with
    map_eq_zero_of_eq' := by
      intro x i k hx hik
      exact alternating_of_dense_span_range j j.injective
        (hj.mono Submodule.subset_span) q
        (G.subtype.compAlternatingMap m.toAlternatingMap)
        (fun x => denseScalarFamilyExtension_apply hKL (fun _ : I => j)
          (fun _ => hj) _ x) x i k hx hik }

@[simp]
theorem denseAlternatingScalarExtension_apply (m : E [⋀^I]→L[K] G) (x : I → E) :
    denseAlternatingScalarExtension hKL j hj G m (fun i => j (x i)) = (m x : L) :=
  denseScalarFamilyExtension_apply hKL (fun _ : I => j) (fun _ => hj) _ x

/-- The complete-field extension retains the original operator norm. -/
@[simp]
theorem norm_denseAlternatingScalarExtension (m : E [⋀^I]→L[K] G) :
    ‖denseAlternatingScalarExtension hKL j hj G m‖ = ‖m‖ := by
  change ‖denseScalarFamilyExtension hKL (fun _ : I => j) (fun _ => hj)
    (G.subtypeL.compContinuousMultilinearMap m.toContinuousMultilinearMap)‖ =
      ‖m.toContinuousMultilinearMap‖
  exact norm_denseScalarFamilyExtension_comp hKL (fun _ : I => j) (fun _ => hj)
    G.subtypeₗᵢ m.toContinuousMultilinearMap

include hs in
/-- Determinant uniqueness describes the extension at every ambient tuple. -/
theorem denseAlternatingScalarExtension_eq_coefficient_det
    (m : E [⋀^I]→L[K] G) (x : I → H) :
    denseAlternatingScalarExtension hKL j hj G m x = (m s : L) * b.det x := by
  let q := denseAlternatingScalarExtension hKL j hj G m
  have hq := congrArg (fun f : H [⋀^I]→ₗ[L] L => f x)
    (q.toAlternatingMap.eq_smul_basis_det b)
  have hs' : (fun i => j (s i)) = b := funext hs
  change q x = q b * b.det x at hq
  rw [← hs'] at hq
  simpa only [q, denseAlternatingScalarExtension_apply] using hq

include hKL hj hs in
/-- Top-degree uniqueness is applied over the complete extension field. -/
theorem alternating_eq_coefficient_mul_det (m : E [⋀^I]→L[K] G) (x : I → E) :
    (m x : L) = (m s : L) * b.det (fun i => j (x i)) := by
  let q := denseAlternatingScalarExtension hKL j hj G m
  have hq := congrArg (fun f : H [⋀^I]→ₗ[L] L => f (fun i => j (x i)))
    (q.toAlternatingMap.eq_smul_basis_det b)
  have hs' : (fun i => j (s i)) = b := funext hs
  change q (fun i => j (x i)) = q b * b.det (fun i => j (x i)) at hq
  rw [← hs'] at hq
  simpa only [q, denseAlternatingScalarExtension_apply] using hq

/-- Evaluation on the normalized basis takes values in the coefficient submodule. -/
def determinantCoefficientLinearMap :
    (E [⋀^I]→L[K] G) →ₗ[K] determinantCoefficientSubmodule j.toLinearMap b G where
  toFun m := ⟨(m s : L), fun x => by
    change (m s : L) * b.det (fun i => j (x i)) ∈ G
    rw [← alternating_eq_coefficient_mul_det hKL j hj b G s hs m x]
    exact (m x).property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Restrict scalars on the determinant before restricting its inputs. -/
def determinantOnDenseSource : E [⋀^I]→ₗ[K] L :=
  ({ b.det with
      toMultilinearMap := b.det.toMultilinearMap.restrictScalars K } :
    H [⋀^I]→ₗ[K] L).compLinearMap j.toLinearMap

/-- The algebraic inverse uses the actual determinant and the inherited target submodule. -/
def determinantCoefficientInverse (c : determinantCoefficientSubmodule j.toLinearMap b G)
    (hdet : ∀ x : I → E, ‖b.det (fun i => j (x i))‖ ≤ ∏ i, ‖x i‖) :
    E [⋀^I]→L[K] G :=
  (((c : L) • determinantOnDenseSource j b).codRestrict G
    c.property).mkContinuous ‖(c : L)‖ (fun x => by
      change ‖(c : L) * b.det (fun i => j (x i))‖ ≤ ‖(c : L)‖ * ∏ i, ‖x i‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hdet x) (norm_nonneg _))

omit [CompleteSpace L] in
@[simp]
theorem determinantCoefficientInverse_apply
    (c : determinantCoefficientSubmodule j.toLinearMap b G)
    (hdet : ∀ x : I → E, ‖b.det (fun i => j (x i))‖ ≤ ∏ i, ‖x i‖) (x : I → E) :
    (determinantCoefficientInverse j b G c hdet x : L) =
      (c : L) * b.det (fun i => j (x i)) := rfl

/-- Exact coefficient extraction, including empty index types. -/
def determinantCoefficientEquiv (hnorm : ∀ i, ‖s i‖ = 1)
    (hdet : ∀ x : I → E, ‖b.det (fun i => j (x i))‖ ≤ ∏ i, ‖x i‖) :
    (E [⋀^I]→L[K] G) ≃ₗᵢ[K] determinantCoefficientSubmodule j.toLinearMap b G where
  toLinearEquiv :=
    { determinantCoefficientLinearMap hKL j hj b G s hs with
      invFun c := determinantCoefficientInverse j b G c hdet
      left_inv m := by
        ext x
        exact (alternating_eq_coefficient_mul_det hKL j hj b G s hs m x).symm
      right_inv c := by
        apply Subtype.ext
        change (c : L) * b.det (fun i => j (s i)) = c
        rw [show (fun i => j (s i)) = b from funext hs, b.det_self, mul_one] }
  norm_map' m := by
    change ‖(m s : L)‖ = ‖m‖
    apply le_antisymm
    · change ‖m s‖ ≤ ‖m‖
      simpa only [hnorm, Finset.prod_const_one, mul_one] using m.le_opNorm s
    · apply m.opNorm_le_bound (norm_nonneg _)
      intro x
      change ‖(m x : L)‖ ≤ _
      rw [alternating_eq_coefficient_mul_det hKL j hj b G s hs m x, norm_mul]
      exact mul_le_mul_of_nonneg_left (hdet x) (norm_nonneg _)

@[simp]
theorem determinantCoefficientEquiv_apply (hnorm : ∀ i, ‖s i‖ = 1)
    (hdet : ∀ x : I → E, ‖b.det (fun i => j (x i))‖ ≤ ∏ i, ‖x i‖)
    (m : E [⋀^I]→L[K] G) :
    (determinantCoefficientEquiv hKL j hj b G s hs hnorm hdet m : L) = m s := rfl

end AlternatingAnalytic
