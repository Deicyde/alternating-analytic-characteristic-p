import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import AlternatingAnalytic.Analysis.ProjectiveExterior

/-!
# Bounded linearization on the projective exterior power

The algebraic linearization `⋀^k E → F` of a bounded alternating map `m` is bounded by `‖m‖`
times the projective exterior seminorm. On a weighted wedge decomposition it is bounded by `‖m‖`
times the cost of the decomposition, and the seminorm is the infimum of these costs.
-/

namespace AlternatingAnalytic

variable {K : Type*} [NontriviallyNormedField K] {k : ℕ}
  {E : Type*} [SeminormedAddCommGroup E] [NormedSpace K E]
  {F : Type*} [SeminormedAddCommGroup F] [NormedSpace K F]

/-- The algebraic linearization `⋀^k E → F` of a bounded alternating map. -/
noncomputable def exteriorLinearization (m : E [⋀^Fin k]→L[K] F) : (⋀[K]^k E) →ₗ[K] F :=
  exteriorPower.alternatingMapLinearEquiv m.toAlternatingMap

@[simp]
theorem exteriorLinearization_ιMulti (m : E [⋀^Fin k]→L[K] F) (x : Fin k → E) :
    exteriorLinearization m (exteriorPower.ιMulti K k x) = m x :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ x

theorem exteriorDecompositionValue_of (b : K × (Fin k → E)) :
    exteriorDecompositionValue (FreeAddMonoid.of b) = b.1 • exteriorPower.ιMulti K k b.2 :=
  FreeAddMonoid.lift_eval_of _ _

omit [NormedSpace K E] in
theorem exteriorDecompositionCost_of_add (b : K × (Fin k → E))
    (p : FreeAddMonoid (K × (Fin k → E))) :
    exteriorDecompositionCost (FreeAddMonoid.of b + p) =
      ‖b.1‖ * ∏ i, ‖b.2 i‖ + exteriorDecompositionCost p := by
  simp [exteriorDecompositionCost, PiTensorProduct.projectiveSeminormAux]

/-- On a weighted wedge decomposition, the linearization is bounded by `‖m‖` times its cost. -/
theorem norm_exteriorLinearization_decomposition_le (m : E [⋀^Fin k]→L[K] F)
    (p : FreeAddMonoid (K × (Fin k → E))) :
    ‖exteriorLinearization m (exteriorDecompositionValue p)‖ ≤
      ‖m‖ * exteriorDecompositionCost p := by
  induction p using FreeAddMonoid.inductionOn' with
  | zero => simp [exteriorDecompositionCost, PiTensorProduct.projectiveSeminormAux]
  | of_add b p ih =>
    rw [map_add, map_add, exteriorDecompositionValue_of, map_smul, exteriorLinearization_ιMulti,
      exteriorDecompositionCost_of_add, mul_add]
    refine (norm_add_le _ _).trans (add_le_add ?_ ih)
    rw [norm_smul, mul_left_comm]
    exact mul_le_mul_of_nonneg_left (m.le_opNorm b.2) (norm_nonneg _)

/-- The linearization of `m` is bounded by `‖m‖` times the projective exterior seminorm. -/
theorem norm_exteriorLinearization_le (m : E [⋀^Fin k]→L[K] F) (z : ⋀[K]^k E) :
    ‖exteriorLinearization m z‖ ≤ ‖m‖ * projectiveExteriorSeminorm z := by
  rw [projectiveExteriorSeminorm_def, Real.mul_iInf_of_nonneg (norm_nonneg m)]
  apply le_ciInf
  intro p
  have hp : exteriorDecompositionValue p.val = z := p.property
  simpa only [hp] using norm_exteriorLinearization_decomposition_le m p.val

end AlternatingAnalytic
