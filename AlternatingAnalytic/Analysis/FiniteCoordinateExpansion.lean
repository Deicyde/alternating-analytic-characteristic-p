import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-! Exterior-basis expansion for a finite coordinate basis. The determinant is
oriented with the coordinate index in the row, as in the manuscript. -/

noncomputable section

namespace AlternatingAnalytic

open scoped BigOperators
open Module

/-- The exterior-basis expansion, with no topological or characteristic assumptions. -/
theorem finiteCoordinate_expansion_algebraic
    {K H G : Type*} [CommRing K] [AddCommGroup H] [Module K H]
    [AddCommGroup G] [Module K G] {d : ℕ}
    (b : Basis (Fin d) K H) (k : ℕ) (m : H [⋀^Fin k]→ₗ[K] G)
    (y : Fin k → H) :
    (∑ s : Set.powersetCard (Fin d) k,
      (Matrix.of fun a j => b.coord (Set.powersetCard.ofFinEmbEquiv.symm s a)
        (y j)).det • m (fun a => b (Set.powersetCard.ofFinEmbEquiv.symm s a))) = m y := by
  classical
  let L := exteriorPower.alternatingMapLinearEquiv m
  have h := congrArg L ((b.exteriorPower k).sum_repr (exteriorPower.ιMulti K k y))
  rw [map_sum] at h
  simp only [map_smul] at h
  calc
    _ = ∑ s : Set.powersetCard (Fin d) k,
        (b.exteriorPower k).repr (exteriorPower.ιMulti K k y) s •
          L ((b.exteriorPower k) s) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti,
        exteriorPower.basis_apply]
      simp only [L, exteriorPower.ιMulti_family,
        exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
      congr 1
      exact (Matrix.det_transpose _).symm
    _ = L (exteriorPower.ιMulti K k y) := h
    _ = m y := exteriorPower.alternatingMapLinearEquiv_apply_ιMulti m y

/-- Exterior-basis expansion for continuous alternating maps. This uses only
algebraic coordinates and does not require that they be continuous. -/
theorem finiteCoordinate_expansion
    {K H F : Type*} [NontriviallyNormedField K]
    [NormedAddCommGroup H] [NormedSpace K H]
    [NormedAddCommGroup F] [NormedSpace K F] {d : ℕ}
    (b : Basis (Fin d) K H) (k : ℕ) (m : H [⋀^Fin k]→L[K] F)
    (y : Fin k → H) :
    (∑ s : Set.powersetCard (Fin d) k,
      (Matrix.of fun a j => b.coord (Set.powersetCard.ofFinEmbEquiv.symm s a)
        (y j)).det • m (fun a => b (Set.powersetCard.ofFinEmbEquiv.symm s a))) = m y :=
  finiteCoordinate_expansion_algebraic b k m.toAlternatingMap y

end AlternatingAnalytic
