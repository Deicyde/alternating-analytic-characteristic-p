import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.MetricSpace.Completion

/-! Density of the determinant construction's subspaces, without completeness
of the scalar field. All inclusions carry their actual inherited norms. -/

noncomputable section
open scoped BigOperators

namespace AlternatingAnalytic

/-- A subspace containing the coordinate basis is dense when its coefficient
field has dense image in the ambient coefficient field. -/
theorem denseRange_subtype_of_coordinate_basis
    {K L A : Type*} [Field K] [NontriviallyNormedField L] [Algebra K L]
    [NormedAddCommGroup A] [NormedSpace L A] [Module K A] [IsScalarTower K L A]
    {n : ℕ} (c : A ≃ₗᵢ[L] (Fin n → L)) (S : Submodule K A)
    (hd : DenseRange (algebraMap K L))
    (hb : ∀ i, c.symm (Pi.single i 1) ∈ S) :
    DenseRange S.subtypeₗᵢ := by
  classical
  have hmem (x : Fin n → K) : c.symm (fun i => algebraMap K L (x i)) ∈ S := by
    have hexp : (fun i => algebraMap K L (x i)) =
        ∑ i : Fin n, algebraMap K L (x i) • Pi.single i (1 : L) := by
      ext j
      simp [Pi.single_apply, Algebra.smul_def]
    rw [hexp, map_sum]
    apply S.sum_mem
    intro i _
    rw [map_smul, IsScalarTower.algebraMap_smul]
    exact S.smul_mem (x i) (hb i)
  let f : (Fin n → K) → S := fun x => ⟨_, hmem x⟩
  have hpi : DenseRange (Pi.map (fun _ : Fin n => algebraMap K L)) :=
    DenseRange.piMap (fun _ => hd)
  have hall := c.symm.surjective.denseRange.comp hpi c.symm.continuous
  exact DenseRange.of_comp (g := f) hall

/-- A scalar subspace containing one contains the dense image of the
coefficient field. No completeness of the smaller field is needed. -/
theorem denseRange_subtype_of_one
    {K L : Type*} [Field K] [NontriviallyNormedField L] [Algebra K L]
    (S : Submodule K L) (hd : DenseRange (algebraMap K L)) (h1 : (1 : L) ∈ S) :
    DenseRange S.subtypeₗᵢ := by
  let f : K → S := fun a => ⟨algebraMap K L a, by
    simpa only [Algebra.smul_def, mul_one] using S.smul_mem a h1⟩
  exact DenseRange.of_comp (g := f) hd

/-- The completion of an actual dense subspace is linearly isometric to the
complete ambient space, even when the scalar field is incomplete. -/
def denseSubmoduleCompletionEquiv
    {K A : Type*} [NontriviallyNormedField K] [NormedAddCommGroup A]
    [NormedSpace K A] [CompleteSpace A]
    (S : Submodule K A) (hd : DenseRange S.subtypeₗᵢ) :
    UniformSpace.Completion S ≃ₗᵢ[K] A :=
  LinearIsometryEquiv.ofSurjective S.subtypeₗᵢ.fromCompletion (by
    intro a
    have hr : a ∈ Set.range S.subtypeₗᵢ.fromCompletion := by
      exact hd.induction_on a
        S.subtypeₗᵢ.fromCompletion.isometry.isClosedEmbedding.isClosed_range
        (fun s => ⟨s, S.subtypeₗᵢ.fromCompletion_apply_coe s⟩)
    exact hr)

@[simp]
theorem denseSubmoduleCompletionEquiv_apply_coe
    {K A : Type*} [NontriviallyNormedField K] [NormedAddCommGroup A]
    [NormedSpace K A] [CompleteSpace A]
    (S : Submodule K A) (hd : DenseRange S.subtypeₗᵢ) (s : S) :
    denseSubmoduleCompletionEquiv S hd (s : UniformSpace.Completion S) = (s : A) :=
  S.subtypeₗᵢ.fromCompletion_apply_coe s

end AlternatingAnalytic
