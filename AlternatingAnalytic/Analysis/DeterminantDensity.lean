import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.MetricSpace.Completion

/-!
# Density of subspaces over a dense subfield

Criteria for a `K`-subspace of a normed `L`-space to be dense, where `K` is dense in `L`,
and the identification of the completion of a dense subspace with the ambient space. These
give the completions `A` and `L` of the spaces `E`, `D`, `G` in Appendix H.
-/

noncomputable section
open scoped BigOperators

namespace AlternatingAnalytic

/-- A `K`-subspace containing a coordinate basis of `A ≅ L^n` is dense, if `K` is dense in `L`. -/
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

/-- A `K`-subspace of `L` containing `1` is dense, if `K` is dense in `L`. -/
theorem denseRange_subtype_of_one
    {K L : Type*} [Field K] [NontriviallyNormedField L] [Algebra K L]
    (S : Submodule K L) (hd : DenseRange (algebraMap K L)) (h1 : (1 : L) ∈ S) :
    DenseRange S.subtypeₗᵢ := by
  let f : K → S := fun a => ⟨algebraMap K L a, by
    simpa only [Algebra.smul_def, mul_one] using S.smul_mem a h1⟩
  exact DenseRange.of_comp (g := f) hd

/-- The completion of a dense subspace of a complete space is linearly isometric to it. -/
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
