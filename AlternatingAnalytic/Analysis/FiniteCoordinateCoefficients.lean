import AlternatingAnalytic.Algebra.FullPolarization
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.LinearAlgebra.Quotient.Defs

noncomputable section

namespace FiniteCoordinateReflection

variable {K Z : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup Z] [NormedSpace K Z] {d n : ℕ}

/-- Membership of the diagonal in a subspace forces membership of every grouped
coordinate coefficient. The individual multilinear values need not belong to it. -/
theorem sumOfType_mem
    (W : Submodule K Z) (p : (Fin d → K) [×n]→L[K] Z)
    (hp : ∀ x, p (fun _ => x) ∈ W) (α : Fin d → ℕ) :
    p.toMultilinearMap.sumOfType (fun j => Pi.single j 1) α ∈ W := by
  classical
  have h := MultilinearMap.sumOfType_eq_of_diagonal_eq
    (W.mkQ.compMultilinearMap p.toMultilinearMap) 0
    (fun x => by simpa using (Submodule.Quotient.mk_eq_zero W).mpr (hp x))
    (fun j : Fin d => Pi.single j 1) α
  apply (Submodule.Quotient.mk_eq_zero W).mp
  simpa [MultilinearMap.sumOfType, ← Submodule.mkQ_apply, map_sum] using h

/-- A grouped coefficient is bounded by the sum of the norms of all its
coordinate-selection terms. -/
theorem norm_sumOfType_le
    (p : (Fin d → K) [×n]→L[K] Z) (α : Fin d → ℕ) :
    ‖p.toMultilinearMap.sumOfType (fun j => Pi.single j 1) α‖ ≤
      ∑ _f ∈ Finset.univ.filter
        (fun f : Fin n → Fin d => Polarization.selectionType f = α), ‖p‖ := by
  classical
  unfold MultilinearMap.sumOfType
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro f hf
  apply p.unit_le_opNorm
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro j
  by_cases h : j = f i <;> simp [h]

end FiniteCoordinateReflection
