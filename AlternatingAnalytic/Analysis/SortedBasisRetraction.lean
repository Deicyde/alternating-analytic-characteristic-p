import AlternatingAnalytic.Analysis.WeightedDeterminantBound
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Module.Bases
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-! The sorted retraction on an orthogonal algebraic basis. This is the finite-span
stage of the topological-basis construction in `charp.tex`, lines 1444–1459. -/

noncomputable section

namespace AlternatingAnalytic

open scoped BigOperators
open Module

variable {K I D F : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [LinearOrder I] [NormedAddCommGroup D] [NormedSpace K D]
  [NormedAddCommGroup F] [NormedSpace K F] [IsUltrametricDist F]

/-- Prescribe a multilinear map's values on increasing basis tuples and extend
them by the universal property of the actual exterior power. -/
def sortedAlternatingMap (b : Basis I K D) (n : ℕ) :
    (D [×n]→L[K] F) →ₗ[K] (D [⋀^Fin n]→ₗ[K] F) :=
  exteriorPower.alternatingMapLinearEquiv.symm.toLinearMap.comp
    (((b.exteriorPower n).constr K).toLinearMap.comp
      ({ toFun := fun g s => g (b ∘ Set.powersetCard.ofFinEmbEquiv.symm s)
         map_add' := by intros; rfl
         map_smul' := by intros; rfl } :
          (D [×n]→L[K] F) →ₗ[K] (Set.powersetCard I n → F)))

omit [IsUltrametricDist K] in
theorem sortedAlternatingMap_apply (b : Basis I K D) (n : ℕ)
    (g : D [×n]→L[K] F) (v : Fin n → D) :
    sortedAlternatingMap b n g v =
      ((b.exteriorPower n).repr (exteriorPower.ιMulti K n v)).sum
        (fun s c => c • g (b ∘ Set.powersetCard.ofFinEmbEquiv.symm s)) := by
  simp [sortedAlternatingMap, exteriorPower.alternatingMapLinearEquiv_symm_apply,
    Basis.constr_apply]

omit [IsUltrametricDist K] in
theorem sortedAlternatingMap_basis (b : Basis I K D) (n : ℕ)
    (g : D [×n]→L[K] F) (s : Set.powersetCard I n) :
    sortedAlternatingMap b n g (b ∘ Set.powersetCard.ofFinEmbEquiv.symm s) =
      g (b ∘ Set.powersetCard.ofFinEmbEquiv.symm s) := by
  change (b.exteriorPower n).constr K
    (fun t => g (b ∘ Set.powersetCard.ofFinEmbEquiv.symm t))
    (exteriorPower.ιMulti_family K n b s) = _
  rw [← exteriorPower.basis_apply, Basis.constr_basis]

omit [IsUltrametricDist K] in
theorem sortedAlternatingMap_retract (b : Basis I K D) (n : ℕ)
    (g : D [⋀^Fin n]→L[K] F) :
    sortedAlternatingMap b n g.toContinuousMultilinearMap = g.toAlternatingMap := by
  apply exteriorPower.alternatingMapLinearEquiv.injective
  change exteriorPower.alternatingMapLinearEquiv
    (exteriorPower.alternatingMapLinearEquiv.symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  apply (b.exteriorPower n).ext
  intro s
  change (b.exteriorPower n).constr K
    (fun t => g (b ∘ Set.powersetCard.ofFinEmbEquiv.symm t))
    ((b.exteriorPower n) s) = _
  rw [Basis.constr_basis, exteriorPower.basis_apply]
  simp [exteriorPower.ιMulti_family]

theorem norm_sortedAlternatingMap_le (b : Basis I K D)
    (hb : ∀ i x, ‖b.coord i x‖ * ‖b i‖ ≤ ‖x‖) (n : ℕ)
    (g : D [×n]→L[K] F) (v : Fin n → D) :
    ‖sortedAlternatingMap b n g v‖ ≤ ‖g‖ * ∏ i, ‖v i‖ := by
  classical
  rw [sortedAlternatingMap_apply, Finsupp.sum]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro s _
  rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti, norm_smul]
  let t := Set.powersetCard.ofFinEmbEquiv.symm s
  have hdet := norm_det_mul_prod_le
    (Matrix.of fun i j => b.coord (t i) (v j)) (fun i => ‖b (t i)‖)
    (fun j => ‖v j‖) (fun i => norm_nonneg _) (fun i j => hb _ _)
  have htrans : (Matrix.of fun i j => b.coord (t j) (v i)).det =
      (Matrix.of fun i j => b.coord (t i) (v j)).det := Matrix.det_transpose _
  change ‖(Matrix.of fun i j => b.coord (t j) (v i)).det‖ * ‖g (b ∘ t)‖ ≤ _
  rw [htrans]
  calc
    _ ≤ ‖(Matrix.of fun i j => b.coord (t i) (v j)).det‖ *
        (‖g‖ * ∏ i, ‖b (t i)‖) :=
      mul_le_mul_of_nonneg_left (g.le_opNorm _) (norm_nonneg _)
    _ = ‖g‖ * (‖(Matrix.of fun i j => b.coord (t i) (v j)).det‖ *
        ∏ i, ‖b (t i)‖) := by ring
    _ ≤ ‖g‖ * ∏ i, ‖v i‖ := mul_le_mul_of_nonneg_left hdet (norm_nonneg _)

/-- Sorting is a linear contraction onto continuous alternating maps. -/
def sortedBasisRetraction (b : Basis I K D)
    (hb : ∀ i x, ‖b.coord i x‖ * ‖b i‖ ≤ ‖x‖) (n : ℕ) :
    (D [×n]→L[K] F) →L[K] (D [⋀^Fin n]→L[K] F) :=
  AlternatingMap.mkContinuousLinear (sortedAlternatingMap b n) 1
    (fun g v => by simpa using norm_sortedAlternatingMap_le b hb n g v)

theorem norm_sortedBasisRetraction_le (b : Basis I K D)
    (hb : ∀ i x, ‖b.coord i x‖ * ‖b i‖ ≤ ‖x‖) (n : ℕ) :
    ‖sortedBasisRetraction (F := F) b hb n‖ ≤ 1 :=
  AlternatingMap.mkContinuousLinear_norm_le _ zero_le_one _

theorem sortedBasisRetraction_apply (b : Basis I K D)
    (hb : ∀ i x, ‖b.coord i x‖ * ‖b i‖ ≤ ‖x‖) (n : ℕ)
    (g : D [×n]→L[K] F) (v : Fin n → D) :
    sortedBasisRetraction b hb n g v = sortedAlternatingMap b n g v := rfl

theorem sortedBasisRetraction_retract (b : Basis I K D)
    (hb : ∀ i x, ‖b.coord i x‖ * ‖b i‖ ≤ ‖x‖) (n : ℕ)
    (g : D [⋀^Fin n]→L[K] F) :
    sortedBasisRetraction b hb n g.toContinuousMultilinearMap = g := by
  ext v
  exact DFunLike.congr_fun (sortedAlternatingMap_retract b n g) v

omit [IsUltrametricDist K] in
/-- On the algebraic span of a Schauder basis, its Hamel coordinates agree with
the given continuous coordinate functionals. -/
theorem schauderSpanBasis_coord (b : UnconditionalSchauderBasis I K D)
    (i : I) (x : Submodule.span K (Set.range b)) :
    (Basis.span b.linearIndependent).coord i x = b.coord i x := by
  classical
  have h : (Basis.span b.linearIndependent).coord i =
      (b.coord i).toLinearMap.comp (Submodule.span K (Set.range b)).subtype := by
    apply (Basis.span b.linearIndependent).ext
    intro j
    simp [b.ortho, Pi.single_apply, Finsupp.single_apply, eq_comm]
  exact LinearMap.congr_fun h x

omit [IsUltrametricDist K] in
theorem schauderSpanBasis_bound (b : UnconditionalSchauderBasis I K D)
    (hb : ∀ i x, ‖b.coord i x‖ * ‖b i‖ ≤ ‖x‖)
    (i : I) (x : Submodule.span K (Set.range b)) :
    ‖(Basis.span b.linearIndependent).coord i x‖ *
      ‖Basis.span b.linearIndependent i‖ ≤ ‖x‖ := by
  rw [schauderSpanBasis_coord]
  simpa only [← Submodule.norm_coe, Basis.coe_span_apply] using hb i x

omit [IsUltrametricDist K] [LinearOrder I] in
/-- Unconditional expansion gives density of the finite coordinate span, with
no countability or completeness assumption on the ambient space. -/
theorem schauderSpan_denseRange (b : UnconditionalSchauderBasis I K D) :
    DenseRange (Submodule.span K (Set.range b)).subtypeₗᵢ := by
  classical
  intro x
  apply mem_closure_of_tendsto (b.tendsto_proj x)
  apply Filter.Eventually.of_forall
  intro A
  refine ⟨⟨b.proj A x, ?_⟩, rfl⟩
  rw [b.proj_apply]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

end AlternatingAnalytic
