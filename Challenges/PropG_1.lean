import Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSeminorm
import Mathlib.Analysis.Normed.Module.Completion

/-!
# Proposition G.1 (homogeneous reflection), p. 55

Paper statement (Appendix G: `K` is complete and nontrivially normed, `P` is Banach, `T_n(P)`
is the separated completed projective tensor power, `Δ_n(P)` is the closed span of the pure
powers `x^{⊗ n}`, and a projection onto `Δ_n(P)` is a bounded linear map
`R_n : T_n(P) → Δ_n(P)` that is the identity on `Δ_n(P)`):
"For a fixed n ≥ 1, the following conditions are equivalent.
(1) For every Banach space Z, closed subspace W ⊆ Z, and bounded n-linear map B : Pⁿ → Z
with diagonal values in W, there is a bounded W-valued n-linear map with the same diagonal.
(2) The subspace Δ_n(P) is the range of a bounded projection in T_n(P)."

## Formalization notes

* `K` and `P` live in `Type u`. The degree index is `Fin n`, with `1 ≤ n` as a hypothesis.
* A bounded `n`-linear map is a `ContinuousMultilinearMap K (fun _ : Fin n => P) Z`; its diagonal
  is `x ↦ B (fun _ => x)`. The `W`-valued map takes values in the subtype `↥W`.
* Universes: `part1` (the equivalence) takes test targets `Z : Type u`, which contains the test
  target `T_n(P)` used for (1) ⇒ (2). `part2` gives (2) ⇒ (1) for targets in any universe.
* Condition (2) is a continuous linear `R : T_n(P) →L[K] Δ_n(P)` with `R t = t` on `Δ_n(P)`.
* `TensorPower` is the completion of Mathlib's `PiTensorProduct` with its projective seminorm.
  `TensorPower`, `diagonalTensor` and `DiagonalSpan` are definitionally the library's
  `AlternatingAnalytic.TensorPower`, `AlternatingAnalytic.diagonalTensor` and
  `AlternatingAnalytic.DiagonalSpan`.
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
  sorry

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
  sorry

end AlternatingAnalyticChallenge.PropG_1
