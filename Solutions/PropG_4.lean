import Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSeminorm
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Group.Ultra
import AlternatingAnalytic.Tensor.L1Projection.Optimal

/-!
# Proposition G.4 (projection norms for ℓ¹), p. 56

Paper statement (Appendix G; `T_n(P)` is the separated completed ordinary projective tensor
power, `Δ_n(P)` the closed span of pure powers, a projection onto `Δ_n(P)` a bounded linear
map `T_n(P) → Δ_n(P)` restricting to the identity on `Δ_n(P)`; `ℓ¹(I,K)` carries the ordinary
sum norm; universal analytic reflection is Definition G.2):
"If K is nonarchimedean and complete, and I is infinite, then
inf{‖R‖ : R : T_n(ℓ¹(I,K)) → Δ_n(ℓ¹(I,K)) is a bounded projection} = n!.
Consequently ℓ¹(I,K) does not have universal analytic reflection."

Formalization notes:
* `K : Type uK` with `[NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]`;
  `I : Type uI` with `[Infinite I]`; `ℓ¹(I,K)` is Mathlib's `lp (fun _ : I => K) 1`
  (sum norm). The degree `n` satisfies `1 ≤ n` (the appendix works with `n ≥ 1`).
* `part1`: the infimum is `sInf` in `ℝ` of the set of norms of projections; since
  `sInf ∅ = 0 ≠ n!` in Mathlib, the equation also asserts that a projection exists.
  The real number `n!` is `(n.factorial : ℝ)`.
* `part2`: `¬ UniversalAnalyticReflection K (lp (fun _ : I => K) 1)`, with Definition G.2
  encoded as in Theorem G.3 (total maps, `AnalyticOnNhd` on open `U`, test targets in
  `Type (max uK uP)`, which here is `Type (max uK uI)`). Restricting test targets weakens
  Definition G.2, so this negation is (harmlessly) stronger than the paper's statement; the
  `c₀` test space of the necessity proof lies in `Type (max uK uI)`.
* Definitions introduced (Mathlib vocabulary, no library import): `TensorPower`,
  `diagonalTensor`, `DiagonalSpan`, `UniversalAnalyticReflection`, identical to the
  Proposition G.1 / Theorem G.3 challenge files.
Solution: proved in `AlternatingAnalytic/Tensor/L1Projection/` (definitions there are copies of
the ones below with the same universe pattern):
* `part1`: `AlternatingAnalytic.L1Projection.sInf_norm_projection_eq_factorial` (`Optimal.lean`),
  from the sorted-orbit projection `exists_projection_norm_le_factorial` (via
  `L1PolynomialLift.exists_l1_diagonal_lift`) and the lower bound
  `factorial_le_norm_of_projection` (ℓ¹ coordinate functionals of `Coordinates.lean`, the
  ultrametric inequality, orbit constancy on `Δ_n`). The hypothesis `1 ≤ n` is not needed.
* `part2`: `AlternatingAnalytic.L1Projection.not_universalAnalyticReflection`, using the
  necessity half of Theorem G.3 re-proved with `K` and `P` in independent universes
  (`TestFamily.lean`, `tensor_projections_of_universalAnalyticReflection`).
-/

namespace AlternatingAnalyticChallenge.PropG_4

universe uK uP uI

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

/-- Definition G.2 (as in Theorem G.3): universal analytic reflection, with maps on an open
`U` encoded as total maps and test targets in `Type (max uK uP)`. -/
def UniversalAnalyticReflection (K : Type uK) (P : Type uP) [NontriviallyNormedField K]
    [NormedAddCommGroup P] [NormedSpace K P] : Prop :=
  ∀ (Z : Type (max uK uP)) [NormedAddCommGroup Z] [NormedSpace K Z] [CompleteSpace Z],
    ∀ (W : Submodule K Z), IsClosed (W : Set Z) →
    ∀ (U : Set P), IsOpen U → ∀ f : P → W,
      AnalyticOnNhd K (fun x => (f x : Z)) U → AnalyticOnNhd K f U

/-- **Proposition G.4**, first part: the optimal norm of a projection
`T_n(ℓ¹(I,K)) → Δ_n(ℓ¹(I,K))` is `n!`. -/
theorem l1_inf_norm_tensor_projection_eq_factorial_part1
    (K : Type uK) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (I : Type uI) [Infinite I] (n : ℕ) (hn : 1 ≤ n) :
    sInf {c : ℝ | ∃ R : TensorPower K (lp (fun _ : I => K) 1) n →L[K]
        DiagonalSpan K (lp (fun _ : I => K) 1) n,
        (∀ t : DiagonalSpan K (lp (fun _ : I => K) 1) n,
          R (t : TensorPower K (lp (fun _ : I => K) 1) n) = t) ∧ ‖R‖ = c} =
      (n.factorial : ℝ) :=
  AlternatingAnalytic.L1Projection.sInf_norm_projection_eq_factorial (K := K) (I := I) n

/-- **Proposition G.4**, second part: `ℓ¹(I,K)` does not have universal analytic
reflection. -/
theorem l1_not_universalAnalyticReflection_part2
    (K : Type uK) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (I : Type uI) [Infinite I] :
    ¬ UniversalAnalyticReflection K (lp (fun _ : I => K) 1) :=
  AlternatingAnalytic.L1Projection.not_universalAnalyticReflection (K := K) (I := I)

end AlternatingAnalyticChallenge.PropG_4
