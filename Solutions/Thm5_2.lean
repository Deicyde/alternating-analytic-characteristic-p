import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Operator.Bilinear
import AlternatingAnalytic.Exterior.DualTests

/-!
# Theorem 5.2 (universal and scalar tests), pp. 13–14

Solution: the statements of `Challenges/Thm5_2.lean`, proved by
`AlternatingAnalytic.DualTests.part1_analytic` … `part3_contDiff`
(`AlternatingAnalytic/Exterior/DualTests.lean`). Each comparison is a fixed bounded linear map
(a flip, a sandwich `T ↦ A ∘ T ∘ B`, or evaluation), so regularity transfers along it. The
library definitions `precompFamily`, `bidualMap` have the same bodies as the challenge's.
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

/-- **Theorem 5.2(1), analytic.** `W` analytic ⇒ `R_F` analytic for every normed `F`;
and `R_Y` analytic ⇒ `W` analytic. -/
theorem part1_analytic {U : Set P} (hU : IsOpen U) (W : P → X →L[K] Y) :
    (AnalyticOnNhd K W U →
      ∀ (F : Type uF) [NormedAddCommGroup F] [NormedSpace K F],
        AnalyticOnNhd K (precompFamily K F W) U) ∧
    (AnalyticOnNhd K (precompFamily K Y W) U → AnalyticOnNhd K W U) := by
  exact AlternatingAnalytic.DualTests.part1_analytic (U := U) W

/-- **Theorem 5.2(2), analytic.** `R_K` analytic ⇔ `J_Y ∘ W` analytic in `L(X, Y**)`;
`R_K` analytic ⇒ `R_{G*}` analytic for every normed `G`; and for any `G` with a nonzero
continuous dual, `R_{G*}` analytic ⇒ `R_K` analytic. -/
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
  exact AlternatingAnalytic.DualTests.part2_analytic (U := U) W

/-- **Theorem 5.2(3), analytic.** A bounded linear left inverse of `J_Y` makes `R_K`-analyticity
imply analyticity of `W`; a bounded linear left inverse of `J_F` makes it imply analyticity of
`R_F`. -/
theorem part3_analytic {U : Set P} (hU : IsOpen U) (W : P → X →L[K] Y) :
    (∀ PY : StrongDual K (StrongDual K Y) →L[K] Y,
      PY.comp (bidualMap K Y) = ContinuousLinearMap.id K Y →
      AnalyticOnNhd K (precompFamily K K W) U → AnalyticOnNhd K W U) ∧
    (∀ (F : Type uF) [NormedAddCommGroup F] [NormedSpace K F]
      (PF : StrongDual K (StrongDual K F) →L[K] F),
      PF.comp (bidualMap K F) = ContinuousLinearMap.id K F →
      AnalyticOnNhd K (precompFamily K K W) U →
      AnalyticOnNhd K (precompFamily K F W) U) := by
  exact AlternatingAnalytic.DualTests.part3_analytic (U := U) W

/-! ### The classes `C^n`, `n ≤ ∞` -/

/-- **Theorem 5.2(1), `C^n`.** -/
theorem part1_contDiff (n : ℕ∞) {U : Set P} (hU : IsOpen U) (W : P → X →L[K] Y) :
    (ContDiffOn K n W U →
      ∀ (F : Type uF) [NormedAddCommGroup F] [NormedSpace K F],
        ContDiffOn K n (precompFamily K F W) U) ∧
    (ContDiffOn K n (precompFamily K Y W) U → ContDiffOn K n W U) := by
  exact AlternatingAnalytic.DualTests.part1_contDiff (U := U) W n

/-- **Theorem 5.2(2), `C^n`.** -/
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
  exact AlternatingAnalytic.DualTests.part2_contDiff (U := U) W n

/-- **Theorem 5.2(3), `C^n`.** -/
theorem part3_contDiff (n : ℕ∞) {U : Set P} (hU : IsOpen U) (W : P → X →L[K] Y) :
    (∀ PY : StrongDual K (StrongDual K Y) →L[K] Y,
      PY.comp (bidualMap K Y) = ContinuousLinearMap.id K Y →
      ContDiffOn K n (precompFamily K K W) U → ContDiffOn K n W U) ∧
    (∀ (F : Type uF) [NormedAddCommGroup F] [NormedSpace K F]
      (PF : StrongDual K (StrongDual K F) →L[K] F),
      PF.comp (bidualMap K F) = ContinuousLinearMap.id K F →
      ContDiffOn K n (precompFamily K K W) U →
      ContDiffOn K n (precompFamily K F W) U) := by
  exact AlternatingAnalytic.DualTests.part3_contDiff (U := U) W n

end AlternatingAnalyticChallenge.Thm5_2
