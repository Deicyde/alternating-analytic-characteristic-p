import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Theorem 5.2 (universal and scalar tests), p. 14

Paper statement: "Let U be an open parameter domain and W : U → L(X, Y) a family. Define
R_F(t)(T) = T ∘ W(t), R_F : U → L(L(Y, F), L(X, F)). For power-series analyticity, or for any
fixed class C^n, the following statements hold.
(1) W is regular if and only if R_F is regular for every normed F; the single target Y
    suffices.
(2) R_K is regular if and only if J_Y W is regular in L(X, Y**), and if and only if R_{G*} is
    regular for every normed G. Any one nonzero continuous dual G* suffices for the last test.
(3) If J_Y has a bounded linear left inverse, regularity of R_K implies regularity of W. If J_F
    has such a left inverse, regularity of R_K implies regularity of R_F."

Here `Y* = L(Y, K)` and `J_Y(y)(λ) = λ(y)` is the canonical map into the continuous bidual.
`K` is any nontrivially normed field.

## Formalization notes
* `U` is an open set in a normed space `P` and `W : P → L(X, Y)`. All spaces are normed
  `K`-spaces, not assumed complete.
* Analyticity on `U` is `AnalyticOnNhd K _ U`; class `C^n` is `ContDiffOn K n _ U` for
  `n : ℕ∞`. Each part is stated once for each (`_analytic`, `_contDiff`).
* `R_F` is `precompFamily K F W`; `J_Y` is `bidualMap K Y`, which is Mathlib's
  `NormedSpace.inclusionInDoubleDual`; `Y*` is `StrongDual K Y`.
* Each "iff for every `F`" with "a single test suffices" is split into two implications. The
  test spaces `F`, `G` range over one arbitrary universe.
* `set_option maxSynthPendingDepth 2` lets Lean find the norm instance on `L(X, Y**)`.
* A bounded linear left inverse of `J_Y` is `P_Y : Y** →L[K] Y` with `P_Y ∘ J_Y = id`.
-/

set_option maxSynthPendingDepth 2

namespace AlternatingAnalyticChallenge.Thm5_2

universe uK uP uX uY uF uG

variable {K : Type uK} [NontriviallyNormedField K]
  {P : Type uP} [NormedAddCommGroup P] [NormedSpace K P]
  {X : Type uX} [NormedAddCommGroup X] [NormedSpace K X]
  {Y : Type uY} [NormedAddCommGroup Y] [NormedSpace K Y]

/-- `R_F(t)(T) = T ∘ W(t)`, as a family `P → L(L(Y, F), L(X, F))`. -/
noncomputable def precompFamily (K : Type*) [NontriviallyNormedField K]
    {P X Y : Type*} [NormedAddCommGroup X] [NormedSpace K X]
    [NormedAddCommGroup Y] [NormedSpace K Y]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace K F]
    (W : P → X →L[K] Y) (t : P) : (Y →L[K] F) →L[K] (X →L[K] F) :=
  (ContinuousLinearMap.compL K X Y F).flip (W t)

/-- The canonical map `J_Y : Y → Y**`, `J_Y(y)(λ) = λ(y)`. -/
noncomputable def bidualMap (K : Type*) [NontriviallyNormedField K]
    (Y : Type*) [NormedAddCommGroup Y] [NormedSpace K Y] :
    Y →L[K] StrongDual K (StrongDual K Y) :=
  ContinuousLinearMap.apply K K

/-! ### Power-series analyticity -/

/-- Theorem 5.2(1), analytic: if `W` is analytic then every `R_F` is, and if `R_Y` is analytic
then so is `W`. -/
theorem part1_analytic {U : Set P} (hU : IsOpen U) (W : P → X →L[K] Y) :
    (AnalyticOnNhd K W U →
      ∀ (F : Type uF) [NormedAddCommGroup F] [NormedSpace K F],
        AnalyticOnNhd K (precompFamily K F W) U) ∧
    (AnalyticOnNhd K (precompFamily K Y W) U → AnalyticOnNhd K W U) := by
  sorry

/-- Theorem 5.2(2), analytic: `R_K` is analytic iff `J_Y ∘ W` is, iff `R_{G*}` is for every
`G`; one `G` with a nonzero dual suffices. -/
theorem part2_analytic {U : Set P} (hU : IsOpen U) (W : P → X →L[K] Y) :
    (AnalyticOnNhd K (precompFamily K K W) U ↔
      AnalyticOnNhd K (fun t => (bidualMap K Y).comp (W t)) U) ∧
    (AnalyticOnNhd K (precompFamily K K W) U →
      ∀ (G : Type uG) [NormedAddCommGroup G] [NormedSpace K G],
        AnalyticOnNhd K (precompFamily K (StrongDual K G) W) U) ∧
    (∀ (G : Type uG) [NormedAddCommGroup G] [NormedSpace K G],
      (∃ φ : StrongDual K G, φ ≠ 0) →
      AnalyticOnNhd K (precompFamily K (StrongDual K G) W) U →
      AnalyticOnNhd K (precompFamily K K W) U) := by
  sorry

/-- Theorem 5.2(3), analytic: with a bounded left inverse of `J_Y` (resp. `J_F`), analyticity
of `R_K` implies that of `W` (resp. `R_F`). -/
theorem part3_analytic {U : Set P} (hU : IsOpen U) (W : P → X →L[K] Y) :
    (∀ PY : StrongDual K (StrongDual K Y) →L[K] Y,
      PY.comp (bidualMap K Y) = ContinuousLinearMap.id K Y →
      AnalyticOnNhd K (precompFamily K K W) U → AnalyticOnNhd K W U) ∧
    (∀ (F : Type uF) [NormedAddCommGroup F] [NormedSpace K F]
      (PF : StrongDual K (StrongDual K F) →L[K] F),
      PF.comp (bidualMap K F) = ContinuousLinearMap.id K F →
      AnalyticOnNhd K (precompFamily K K W) U →
      AnalyticOnNhd K (precompFamily K F W) U) := by
  sorry

/-! ### The classes `C^n`, `n ≤ ∞` -/

/-- Theorem 5.2(1) for `C^n`. -/
theorem part1_contDiff (n : ℕ∞) {U : Set P} (hU : IsOpen U) (W : P → X →L[K] Y) :
    (ContDiffOn K n W U →
      ∀ (F : Type uF) [NormedAddCommGroup F] [NormedSpace K F],
        ContDiffOn K n (precompFamily K F W) U) ∧
    (ContDiffOn K n (precompFamily K Y W) U → ContDiffOn K n W U) := by
  sorry

/-- Theorem 5.2(2) for `C^n`. -/
theorem part2_contDiff (n : ℕ∞) {U : Set P} (hU : IsOpen U) (W : P → X →L[K] Y) :
    (ContDiffOn K n (precompFamily K K W) U ↔
      ContDiffOn K n (fun t => (bidualMap K Y).comp (W t)) U) ∧
    (ContDiffOn K n (precompFamily K K W) U →
      ∀ (G : Type uG) [NormedAddCommGroup G] [NormedSpace K G],
        ContDiffOn K n (precompFamily K (StrongDual K G) W) U) ∧
    (∀ (G : Type uG) [NormedAddCommGroup G] [NormedSpace K G],
      (∃ φ : StrongDual K G, φ ≠ 0) →
      ContDiffOn K n (precompFamily K (StrongDual K G) W) U →
      ContDiffOn K n (precompFamily K K W) U) := by
  sorry

/-- Theorem 5.2(3) for `C^n`. -/
theorem part3_contDiff (n : ℕ∞) {U : Set P} (hU : IsOpen U) (W : P → X →L[K] Y) :
    (∀ PY : StrongDual K (StrongDual K Y) →L[K] Y,
      PY.comp (bidualMap K Y) = ContinuousLinearMap.id K Y →
      ContDiffOn K n (precompFamily K K W) U → ContDiffOn K n W U) ∧
    (∀ (F : Type uF) [NormedAddCommGroup F] [NormedSpace K F]
      (PF : StrongDual K (StrongDual K F) →L[K] F),
      PF.comp (bidualMap K F) = ContinuousLinearMap.id K F →
      ContDiffOn K n (precompFamily K K W) U →
      ContDiffOn K n (precompFamily K F W) U) := by
  sorry

end AlternatingAnalyticChallenge.Thm5_2
