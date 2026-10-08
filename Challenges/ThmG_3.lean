import Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSeminorm
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Order.LiminfLimsup

/-!
# Theorem G.3 (analytic tensor criterion), p. 54 (proof pp. 54-55)

Paper statement (Appendix G; `K` complete and nontrivially normed, `P` Banach, `T_n(P)` the
separated completed ordinary projective tensor power, `Δ_n(P)` the closed span of the pure
powers, a projection onto `Δ_n(P)` a bounded linear `R_n : T_n(P) → Δ_n(P)` restricting to the
identity on `Δ_n(P)`; Definition G.2: `P` has universal analytic reflection if for every Banach
space `Z`, closed subspace `W ⊆ Z`, every open `U ⊆ P` and every map `f : U → W`, analyticity of
the composite `U → W ↪ Z` implies analyticity of `f`):
"A Banach space P has universal analytic reflection if and only if there are projections
R_n : T_n(P) → Δ_n(P) for all n ≥ 1 such that limsup_{n→∞} ‖R_n‖^{1/n} < ∞."

Formalization notes:
* `K P : Type u`, `[CompleteSpace K]`, `[CompleteSpace P]`.
* Definition G.2 is `UniversalAnalyticReflection K P` (defined below). Maps `f : U → W` are
  encoded as total maps `f : P → W` with `AnalyticOnNhd` on the open set `U` (analyticity on an
  open set is local, so values off `U` are irrelevant; extend by zero). Universe deviation:
  in `UniversalAnalyticReflection`, "every Banach space Z" is restricted to
  `Z : Type (max uK uP)`, i.e. `Type u` here; this universe contains the `c₀`-sum test space
  used in the necessity proof. `part1` (the equivalence) uses this definition. `part2` records
  the sufficiency direction (projections ⇒ reflection) for targets `Z` in an arbitrary universe
  `v`, so the projection condition gives reflection for every Banach space in every universe.
* The family is indexed by `m : ℕ` with degree `n = m + 1`, so "for all n ≥ 1" is built in.
  "Projection" is `R m : T_{m+1}(P) →L[K] Δ_{m+1}(P)` with `R m t = t` on `Δ_{m+1}(P)`.
* `limsup ‖R_n‖^{1/n} < ∞` is taken in `ℝ≥0∞` (so an unbounded sequence has limsup `⊤`
  rather than a junk real value): `limsup (fun m => (‖R m‖₊ : ℝ≥0∞) ^ ((m+1 : ℝ)⁻¹)) atTop < ⊤`.
* Definitions introduced (Mathlib vocabulary, no library import): `TensorPower`,
  `diagonalTensor`, `DiagonalSpan` (as in Proposition G.1) and `UniversalAnalyticReflection`;
  definitionally equal to the library's `AlternatingAnalytic.TensorPower`, `.DiagonalSpan`,
  `.UniversalAnalyticReflection`.
-/

open Filter
open scoped NNReal ENNReal

namespace AlternatingAnalyticChallenge.ThmG_3

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

/-- Definition G.2: `P` has *universal analytic reflection* if for every Banach space `Z`,
closed subspace `W ⊆ Z`, open `U ⊆ P` and map `f : U → W`, analyticity of the composite
`U → W ↪ Z` implies analyticity of `f`. Maps on `U` are encoded as total maps `P → W`
(only their values on `U` matter); test targets range over `Type (max uK uP)`. -/
def UniversalAnalyticReflection (K : Type uK) (P : Type uP) [NontriviallyNormedField K]
    [NormedAddCommGroup P] [NormedSpace K P] : Prop :=
  ∀ (Z : Type (max uK uP)) [NormedAddCommGroup Z] [NormedSpace K Z] [CompleteSpace Z],
    ∀ (W : Submodule K Z), IsClosed (W : Set Z) →
    ∀ (U : Set P), IsOpen U → ∀ f : P → W,
      AnalyticOnNhd K (fun x => (f x : Z)) U → AnalyticOnNhd K f U

/-- **Theorem G.3** (analytic tensor criterion), the equivalence with Definition G.2. -/
theorem universal_analytic_reflection_iff_tensor_projections_part1
    (K P : Type u) [NontriviallyNormedField K] [CompleteSpace K]
    [NormedAddCommGroup P] [NormedSpace K P] [CompleteSpace P] :
    UniversalAnalyticReflection K P ↔
      ∃ R : ∀ m : ℕ, TensorPower K P (m + 1) →L[K] DiagonalSpan K P (m + 1),
        (∀ (m : ℕ) (t : DiagonalSpan K P (m + 1)), R m (t : TensorPower K P (m + 1)) = t) ∧
        Filter.limsup
          (fun m : ℕ => (‖R m‖₊ : ℝ≥0∞) ^ (((m + 1 : ℕ) : ℝ)⁻¹)) Filter.atTop < ⊤ := by
  sorry

/-- **Theorem G.3**, sufficiency for Banach targets in an arbitrary universe `v`:
projections with finite root-limsup reflect analyticity into every closed subspace. -/
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
