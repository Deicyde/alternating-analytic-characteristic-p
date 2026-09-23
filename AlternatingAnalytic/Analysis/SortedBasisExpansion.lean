import AlternatingAnalytic.Analysis.SortedBasisSummability
import AlternatingAnalytic.Analysis.SortedBasisRetraction
import Mathlib.Order.Filter.AtTopBot.Finset

/-! The actual infinite sorted determinant expansion of a continuous alternating map. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open Filter Topology Module

namespace AlternatingAnalytic

variable {K I E F : Type*} [NontriviallyNormedField K]
  [LinearOrder I] [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup F] [NormedSpace K F]

/-- The n-element subsets contained in a specified finite set. -/
def sortedFiniteSubsets (n : ℕ) (A : Finset I) : Finset (Set.powersetCard I n) :=
  (A.powersetCard n).subtype (fun s : Finset I => s.card = n)

omit [LinearOrder I] in
@[simp]
theorem mem_sortedFiniteSubsets (n : ℕ) (A : Finset I) (s : Set.powersetCard I n) :
    s ∈ sortedFiniteSubsets n A ↔ s.val ⊆ A := by
  simp [sortedFiniteSubsets, Finset.mem_powersetCard]

omit [LinearOrder I] in
/-- These finite subset families are cofinal among all finite collections of n-element sets. -/
theorem tendsto_sortedFiniteSubsets (n : ℕ) :
    Tendsto (sortedFiniteSubsets (I := I) n) atTop atTop := by
  apply Monotone.tendsto_atTop_finset
  · intro A B hAB s hs
    exact (mem_sortedFiniteSubsets n B s).mpr
      (((mem_sortedFiniteSubsets n A s).mp hs).trans hAB)
  · intro s
    exact ⟨s.val, (mem_sortedFiniteSubsets n s.val s).mpr Finset.Subset.rfl⟩

/-- A finite coordinate projection regarded as a vector in the basis span. -/
def schauderProjectionSpan (b : UnconditionalSchauderBasis I K E) (A : Finset I) (x : E) :
    Submodule.span K (Set.range b) :=
  ⟨b.proj A x, by
    rw [b.proj_apply]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))⟩

/-- A finite coordinate projection keeps exactly the indicated coordinates. -/
theorem schauder_coord_proj (b : UnconditionalSchauderBasis I K E) (A : Finset I)
    (i : I) (x : E) : b.coord i (b.proj A x) = if i ∈ A then b.coord i x else 0 := by
  classical
  simp [b.proj_apply, b.ortho, Pi.single_apply, smul_eq_mul]

/-- Projection cuts off a determinant coefficient unless every selected index is retained. -/
theorem sorted_coefficient_proj (b : UnconditionalSchauderBasis I K E) (n : ℕ)
    (A : Finset I) (x : Fin n → E) (s : Set.powersetCard I n) :
    (Matrix.of fun i j => b.coord (Set.powersetCard.ofFinEmbEquiv.symm s i)
      (b.proj A (x j))).det =
    if s.val ⊆ A then
      (Matrix.of fun i j => b.coord (Set.powersetCard.ofFinEmbEquiv.symm s i) (x j)).det
    else 0 := by
  classical
  by_cases hs : s.val ⊆ A
  · rw [ite_eq_left hs]
    apply congrArg Matrix.det
    ext i j
    simp only [Matrix.of_apply]
    rw [schauder_coord_proj, ite_eq_left]
    apply hs
    exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s _).mp ⟨i, rfl⟩
  · rw [ite_eq_right hs]
    obtain ⟨i, hi, hiA⟩ := Finset.not_subset.mp hs
    obtain ⟨j, hj⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s i).mpr hi
    apply Matrix.det_eq_zero_of_row_eq_zero j
    intro l
    simp only [Matrix.of_apply, hj, schauder_coord_proj, ite_eq_right hiA]

/-- The finite sorted expansion follows from the exterior-power basis formula. -/
theorem sum_sortedBasisTerm_eq_projection [IsUltrametricDist F]
    (b : UnconditionalSchauderBasis I K E) (n : ℕ)
    (a : E [⋀^Fin n]→L[K] F) (x : Fin n → E) (A : Finset I) :
    (∑ s ∈ sortedFiniteSubsets n A, sortedBasisTerm b n a.toContinuousMultilinearMap x s) =
      a (fun j => b.proj A (x j)) := by
  classical
  let D := Submodule.span K (Set.range b)
  let bD := Basis.span b.linearIndependent
  let aD := a.compContinuousLinearMap D.subtypeL
  let v : Fin n → D := fun j => schauderProjectionSpan b A (x j)
  let c := (bD.exteriorPower n).repr (exteriorPower.ιMulti K n v)
  have hc (s : Set.powersetCard I n) : c s =
      (Matrix.of fun i j => b.coord (Set.powersetCard.ofFinEmbEquiv.symm s i)
        (b.proj A (x j))).det := by
    dsimp only [c, bD]
    rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
    simp_rw [schauderSpanBasis_coord]
    exact Matrix.det_transpose _
  have hsupp : c.support ⊆ sortedFiniteSubsets n A := by
    intro s hs
    rw [mem_sortedFiniteSubsets]
    by_contra hsa
    have hz : c s = 0 := by rw [hc, sorted_coefficient_proj, ite_eq_right hsa]
    exact Finsupp.mem_support_iff.mp hs hz
  have heval : sortedAlternatingMap bD n aD.toContinuousMultilinearMap v =
      a (fun j => b.proj A (x j)) :=
    DFunLike.congr_fun (sortedAlternatingMap_retract bD n aD) v
  rw [sortedAlternatingMap_apply] at heval
  have hsum : c.sum (fun s z => z • a (b ∘ Set.powersetCard.ofFinEmbEquiv.symm s)) =
      a (fun j => b.proj A (x j)) := by
    change c.sum (fun s z => z • a (fun i =>
      (bD (Set.powersetCard.ofFinEmbEquiv.symm s i) : E))) = _ at heval
    simpa only [bD, Basis.coe_span_apply, Function.comp_def] using heval
  rw [Finsupp.sum_of_support_subset c hsupp
    (fun s z => z • a (b ∘ Set.powersetCard.ofFinEmbEquiv.symm s))
    (fun _ _ => zero_smul K _)] at hsum
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [hc, sorted_coefficient_proj, ite_eq_left ((mem_sortedFiniteSubsets n A s).mp hs)]
  rfl

/-- The exact infinite sorted determinant expansion, for any continuous alternating map. -/
theorem hasSum_sortedBasisTerm [IsUltrametricDist F] [CompleteSpace F]
    (b : UnconditionalSchauderBasis I K E) (n : ℕ)
    (a : E [⋀^Fin n]→L[K] F) (x : Fin n → E) :
    HasSum (sortedBasisTerm b n a.toContinuousMultilinearMap x) (a x) := by
  have hs := summable_sortedBasisTerm b n a.toContinuousMultilinearMap x
  have hpartial := hs.hasSum.comp (tendsto_sortedFiniteSubsets (I := I) n)
  have hlimit : Tendsto (fun A : Finset I => a (fun j => b.proj A (x j)))
      atTop (𝓝 (a x)) :=
    a.cont.tendsto x |>.comp (tendsto_pi_nhds.mpr fun j => b.tendsto_proj (x j))
  have hpartial' : Tendsto (fun A : Finset I => a (fun j => b.proj A (x j))) atTop
      (𝓝 (∑' s, sortedBasisTerm b n a.toContinuousMultilinearMap x s)) := by
    simpa only [Function.comp_def, sum_sortedBasisTerm_eq_projection] using hpartial
  have heq := tendsto_nhds_unique hpartial' hlimit
  rw [← heq]
  exact hs.hasSum

end AlternatingAnalytic
