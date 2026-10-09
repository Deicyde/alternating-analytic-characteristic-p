import Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSeminorm
import Mathlib.Analysis.Normed.Module.Completion

/-!
# Proposition G.1 (homogeneous reflection), p. 55

Paper statement (Appendix G; throughout the appendix `K` is complete and nontrivially normed,
`P` is Banach, `T_n(P)` is the separated completed ordinary projective tensor power and
`Δ_n(P)` is the closed span of the pure powers `x^{⊗ n}`; "a projection onto `Δ_n(P)`" means
a bounded linear map `R_n : T_n(P) → Δ_n(P)` whose restriction to `Δ_n(P)` is the identity):
"For a fixed n ≥ 1, the following conditions are equivalent.
(1) For every Banach space Z, closed subspace W ⊆ Z, and bounded n-linear map B : Pⁿ → Z
with diagonal values in W, there is a bounded W-valued n-linear map with the same diagonal.
(2) The subspace Δ_n(P) is the range of a bounded projection in T_n(P)."

Formalization notes:
* `K : Type u` with `[NontriviallyNormedField K] [CompleteSpace K]`; `P : Type u` a normed
  `K`-space with `[CompleteSpace P]`. Degree index is `Fin n`, with `1 ≤ n` as a hypothesis.
* Bounded `n`-linear maps are `ContinuousMultilinearMap K (fun _ : Fin n => P) Z`; "diagonal"
  is `x ↦ B (fun _ => x)`. The `W`-valued map is a continuous multilinear map into the
  subtype `↥W` with the coercion of its diagonal equal to the diagonal of `B`.
* Universes: Lean cannot quantify over Banach spaces of every universe in one statement.
  `part1` (the equivalence) quantifies over targets `Z : Type u`, the universe of `K` and `P`;
  this universe contains the test target `Z = T_n(P)` used for (1) ⇒ (2). `part2` records
  (2) ⇒ (1) for targets `Z` in an arbitrary universe `v`, so condition (2) gives (1) for
  every Banach space in every universe.
* Condition (2) is stated in the paper's own sense of "projection onto Δ_n(P)": a continuous
  linear `R : T_n(P) →L[K] Δ_n(P)` with `R t = t` for all `t ∈ Δ_n(P)`. (Equivalently,
  `Δ_n(P)` is the range of the idempotent `ι ∘ R` on `T_n(P)`.)
* Definitions introduced (Mathlib vocabulary only, no library import):
  `TensorPower K P n := UniformSpace.Completion (⨂[K] _ : Fin n, P)` (Mathlib's
  `PiTensorProduct` carries the ordinary projective seminorm; the completion is separated),
  `diagonalTensor K n x` (the image of `⨂ₜ x` in the completion) and
  `DiagonalSpan K P n` (topological closure of the span of the pure powers).
  These are definitionally the library's `AlternatingAnalytic.TensorPower`,
  `AlternatingAnalytic.diagonalTensor` and `AlternatingAnalytic.DiagonalSpan`.
-/

namespace AlternatingAnalyticChallenge.PropG_1

universe u v uK uP

open scoped TensorProduct

/-- The separated completed ordinary projective tensor power `T_n(P)`: the Hausdorff
completion of Mathlib's projective seminorm on `⨂[K] (i : Fin n), P`. -/
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

/-- **Proposition G.1**, the equivalence (1) ⇔ (2), with test targets `Z : Type u`. -/
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

/-- **Proposition G.1**, (2) ⇒ (1) for Banach targets in an arbitrary universe `v`. -/
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
