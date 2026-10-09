import Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSeminorm
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Order.LiminfLimsup

/-!
# Theorem G.3 (analytic tensor criterion), p. 55 (proof pp. 55-56)

Paper statement (Appendix G: `K` is complete and nontrivially normed, `P` is Banach, `T_n(P)`
and `Δ_n(P)` are as in Proposition G.1, and a projection onto `Δ_n(P)` is a bounded linear
`R_n : T_n(P) → Δ_n(P)` that is the identity on `Δ_n(P)`. Definition G.2: `P` has universal
analytic reflection if for every Banach space `Z`, closed subspace `W ⊆ Z`, open `U ⊆ P` and
map `f : U → W`, analyticity of the composite `U → W ↪ Z` implies analyticity of `f`):
"A Banach space P has universal analytic reflection if and only if there are projections
R_n : T_n(P) → Δ_n(P) for all n ≥ 1 such that limsup_{n→∞} ‖R_n‖^{1/n} < ∞."

## Formalization notes

* `K` and `P` live in `Type u`.
* Definition G.2 is `UniversalAnalyticReflection K P`. A map `f : U → W` is a total map
  `P → W` that is `AnalyticOnNhd` on the open set `U`.
* Universes: in `UniversalAnalyticReflection` the test targets are `Z : Type (max uK uP)`,
  which contains the `c₀`-sum used for necessity. `part1` (the equivalence) uses this
  definition; `part2` gives sufficiency for targets in any universe.
* The projections are indexed by `m : ℕ` with degree `n = m + 1`, so `n ≥ 1` is built in.
* The limsup is taken in `ℝ≥0∞`, so an unbounded sequence has limsup `⊤`.
* `TensorPower`, `diagonalTensor`, `DiagonalSpan` (as in Proposition G.1) and
  `UniversalAnalyticReflection` are definitionally the library's declarations of the same names
  in namespace `AlternatingAnalytic`.
-/

open Filter
open scoped NNReal ENNReal

namespace AlternatingAnalyticChallenge.ThmG_3

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

/-- Definition G.2: `P` has universal analytic reflection if for every Banach space `Z`,
closed subspace `W ⊆ Z`, open `U ⊆ P` and map `f : U → W`, analyticity of `U → W ↪ Z` implies
analyticity of `f`. Maps on `U` are total maps `P → W`; test targets are in
`Type (max uK uP)`. -/
def UniversalAnalyticReflection (K : Type uK) (P : Type uP) [NontriviallyNormedField K]
    [NormedAddCommGroup P] [NormedSpace K P] : Prop :=
  ∀ (Z : Type (max uK uP)) [NormedAddCommGroup Z] [NormedSpace K Z] [CompleteSpace Z],
    ∀ (W : Submodule K Z), IsClosed (W : Set Z) →
    ∀ (U : Set P), IsOpen U → ∀ f : P → W,
      AnalyticOnNhd K (fun x => (f x : Z)) U → AnalyticOnNhd K f U

/-- Theorem G.3: `P` has universal analytic reflection iff there are projections
`R_n : T_n(P) → Δ_n(P)` with `limsup ‖R_n‖^{1/n} < ∞`. -/
theorem universal_analytic_reflection_iff_tensor_projections_part1
    (K P : Type u) [NontriviallyNormedField K] [CompleteSpace K]
    [NormedAddCommGroup P] [NormedSpace K P] [CompleteSpace P] :
    UniversalAnalyticReflection K P ↔
      ∃ R : ∀ m : ℕ, TensorPower K P (m + 1) →L[K] DiagonalSpan K P (m + 1),
        (∀ (m : ℕ) (t : DiagonalSpan K P (m + 1)), R m (t : TensorPower K P (m + 1)) = t) ∧
        Filter.limsup
          (fun m : ℕ => (‖R m‖₊ : ℝ≥0∞) ^ (((m + 1 : ℕ) : ℝ)⁻¹)) Filter.atTop < ⊤ := by
  sorry

/-- Theorem G.3, sufficiency for Banach targets in any universe: projections with
`limsup ‖R_n‖^{1/n} < ∞` reflect analyticity into every closed subspace. -/
theorem universal_analytic_reflection_of_tensor_projections_part2
    (K P : Type u) [NontriviallyNormedField K] [CompleteSpace K]
    [NormedAddCommGroup P] [NormedSpace K P] [CompleteSpace P]
    (R : ∀ m : ℕ, TensorPower K P (m + 1) →L[K] DiagonalSpan K P (m + 1))
    (hR : ∀ (m : ℕ) (t : DiagonalSpan K P (m + 1)), R m (t : TensorPower K P (m + 1)) = t)
    (hlim : Filter.limsup
      (fun m : ℕ => (‖R m‖₊ : ℝ≥0∞) ^ (((m + 1 : ℕ) : ℝ)⁻¹)) Filter.atTop < ⊤)
    (Z : Type v) [NormedAddCommGroup Z] [NormedSpace K Z] [CompleteSpace Z]
    (W : Submodule K Z) (hW : IsClosed (W : Set Z))
    (U : Set P) (hU : IsOpen U) (f : P → W)
    (hf : AnalyticOnNhd K (fun x => (f x : Z)) U) :
    AnalyticOnNhd K f U := by
  sorry

end AlternatingAnalyticChallenge.ThmG_3
