import Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSeminorm
import Mathlib.Analysis.Normed.Module.Completion
import AlternatingAnalytic.Analysis.HomogeneousTensorReflection

/-!
# Proof of Proposition G.1

Uses `homogeneous_reflection_iff_projection` and `exists_diagonal_lift_of_projection` from
`AlternatingAnalytic/Analysis/HomogeneousTensorReflection.lean`.
-/

namespace AlternatingAnalyticChallenge.PropG_1

universe u v uK uP

open scoped TensorProduct

/-- The completed projective tensor power `T_n(P)`: the Hausdorff completion of
`⨂[K] (i : Fin n), P` with Mathlib's projective seminorm. -/
abbrev TensorPower (K : Type uK) (P : Type uP) [NontriviallyNormedField K]
    [NormedAddCommGroup P] [NormedSpace K P] (n : ℕ) :=
  UniformSpace.Completion (⨂[K] _ : Fin n, P)

/-- The pure power `x^{⊗ n}` in `T_n(P)`. -/
noncomputable def diagonalTensor (K : Type uK) {P : Type uP} [NontriviallyNormedField K]
    [NormedAddCommGroup P] [NormedSpace K P] (n : ℕ) (x : P) : TensorPower K P n :=
  ((⨂ₜ[K] _ : Fin n, x : ⨂[K] _ : Fin n, P) : UniformSpace.Completion (⨂[K] _ : Fin n, P))

/-- `Δ_n(P)`: the closed linear span of the pure powers `x^{⊗ n}` in `T_n(P)`. -/
noncomputable def DiagonalSpan (K : Type uK) (P : Type uP) [NontriviallyNormedField K]
    [NormedAddCommGroup P] [NormedSpace K P] (n : ℕ) : Submodule K (TensorPower K P n) :=
  (Submodule.span K (Set.range (diagonalTensor K (P := P) n))).topologicalClosure

/-- Proposition G.1: (1) ⇔ (2), with test targets `Z : Type u`. -/
theorem homogeneous_reflection_iff_projection_part1
    (K P : Type u) [NontriviallyNormedField K] [CompleteSpace K]
    [NormedAddCommGroup P] [NormedSpace K P] [CompleteSpace P]
    (n : ℕ) (hn : 1 ≤ n) :
    (∀ (Z : Type u) [NormedAddCommGroup Z] [NormedSpace K Z] [CompleteSpace Z]
        (W : Submodule K Z), IsClosed (W : Set Z) →
        ∀ B : ContinuousMultilinearMap K (fun _ : Fin n => P) Z,
          (∀ x : P, B (fun _ => x) ∈ W) →
          ∃ C : ContinuousMultilinearMap K (fun _ : Fin n => P) W,
            ∀ x : P, (C (fun _ => x) : Z) = B (fun _ => x)) ↔
      ∃ R : TensorPower K P n →L[K] DiagonalSpan K P n,
        ∀ t : DiagonalSpan K P n, R (t : TensorPower K P n) = t := by
  have key : ∀ R : TensorPower K P n →L[K] DiagonalSpan K P n,
      R.comp (DiagonalSpan K P n).subtypeL =
          ContinuousLinearMap.id K (DiagonalSpan K P n) ↔
        ∀ t : DiagonalSpan K P n, R (t : TensorPower K P n) = t := fun R =>
    ⟨fun h t => DFunLike.congr_fun h t, fun h => ContinuousLinearMap.ext h⟩
  have := AlternatingAnalytic.homogeneous_reflection_iff_projection (K := K) (P := P) n
  exact this.trans ⟨fun ⟨R, h⟩ => ⟨R, (key R).1 h⟩, fun ⟨R, h⟩ => ⟨R, (key R).2 h⟩⟩

/-- Proposition G.1: (2) ⇒ (1) for Banach targets in any universe. -/
theorem homogeneous_reflection_iff_projection_part2
    (K P : Type u) [NontriviallyNormedField K] [CompleteSpace K]
    [NormedAddCommGroup P] [NormedSpace K P] [CompleteSpace P]
    (n : ℕ) (hn : 1 ≤ n)
    (R : TensorPower K P n →L[K] DiagonalSpan K P n)
    (hR : ∀ t : DiagonalSpan K P n, R (t : TensorPower K P n) = t)
    (Z : Type v) [NormedAddCommGroup Z] [NormedSpace K Z] [CompleteSpace Z]
    (W : Submodule K Z) (hW : IsClosed (W : Set Z))
    (B : ContinuousMultilinearMap K (fun _ : Fin n => P) Z)
    (hB : ∀ x : P, B (fun _ => x) ∈ W) :
    ∃ C : ContinuousMultilinearMap K (fun _ : Fin n => P) W,
      ∀ x : P, (C (fun _ => x) : Z) = B (fun _ => x) := by
  have hR' : R.comp (DiagonalSpan K P n).subtypeL =
      ContinuousLinearMap.id K (DiagonalSpan K P n) := ContinuousLinearMap.ext hR
  obtain ⟨C, hC, -⟩ := AlternatingAnalytic.exists_diagonal_lift_of_projection
    (K := K) (P := P) n R hR' W hW B hB
  exact ⟨C, hC⟩

end AlternatingAnalyticChallenge.PropG_1
