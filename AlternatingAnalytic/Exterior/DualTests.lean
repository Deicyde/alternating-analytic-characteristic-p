import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Universal and scalar tests for operator families (Theorem 5.2)

For a family `W : P → L(X, Y)` and a normed space `F`, the precomposition family
`R_F(t)(T) = T ∘ W(t)` takes values in `L(L(Y, F), L(X, F))`. Every comparison in Theorem 5.2 of
the paper is a fixed bounded linear map carrying one family to another: `R_F` is a bounded linear
function of `W`, `W` is `R_Y` evaluated at `id_Y`, `J_Y ∘ W` and `R_K` are flips of each other,
`R_{G*}` is a bounded linear function of `R_K` (through `L(X, G*) ≅ L(G, X*)`), and `R_K` is
recovered from `R_{G*}` with one nonzero functional on `G`. Hence power-series analyticity on a
set and the classes `C^n` transfer along each comparison.
-/

set_option maxSynthPendingDepth 2

namespace AlternatingAnalytic.DualTests

open ContinuousLinearMap

variable {K : Type*} [NontriviallyNormedField K]
  {P : Type*}
  {X : Type*} [NormedAddCommGroup X] [NormedSpace K X]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace K Y]

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

@[simp]
theorem precompFamily_apply (F : Type*) [NormedAddCommGroup F] [NormedSpace K F]
    (W : P → X →L[K] Y) (t : P) (T : Y →L[K] F) : precompFamily K F W t T = T.comp (W t) :=
  rfl

@[simp]
theorem bidualMap_apply (y : Y) (l : StrongDual K Y) : bidualMap K Y y l = l y :=
  rfl

section Transfer

variable [NormedAddCommGroup P] [NormedSpace K P] {E F : Type*} [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup F] [NormedSpace K F]

/-- Analyticity on a set transfers along a fixed bounded linear map. -/
theorem analyticOnNhd_of_eq_clm {U : Set P} {f : P → E} {g : P → F} (L : F →L[K] E)
    (h : ∀ t, f t = L (g t)) (hg : AnalyticOnNhd K g U) : AnalyticOnNhd K f U := by
  have : f = L ∘ g := funext h
  rw [this]
  exact L.comp_analyticOnNhd hg

/-- The class `C^n` on a set transfers along a fixed bounded linear map. -/
theorem contDiffOn_of_eq_clm {n : WithTop ℕ∞} {U : Set P} {f : P → E} {g : P → F}
    (L : F →L[K] E) (h : ∀ t, f t = L (g t)) (hg : ContDiffOn K n g U) :
    ContDiffOn K n f U := by
  have : f = L ∘ g := funext h
  rw [this]
  exact ContDiff.comp_contDiffOn (L.contDiff (n := n)) hg

end Transfer

section Sandwich

variable {M M' N N' : Type*} [NormedAddCommGroup M] [NormedSpace K M]
  [NormedAddCommGroup M'] [NormedSpace K M'] [NormedAddCommGroup N] [NormedSpace K N]
  [NormedAddCommGroup N'] [NormedSpace K N']

/-- The bounded linear map `T ↦ A ∘ T ∘ B`. -/
noncomputable def sandwichL (A : N →L[K] N') (B : M' →L[K] M) :
    (M →L[K] N) →L[K] (M' →L[K] N') :=
  (compL K M' N N' A).comp ((compL K M' M N).flip B)

@[simp]
theorem sandwichL_apply (A : N →L[K] N') (B : M' →L[K] M) (T : M →L[K] N) :
    sandwichL A B T = A.comp (T.comp B) :=
  rfl

end Sandwich

section Identities

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace K F]
  (G : Type*) [NormedAddCommGroup G] [NormedSpace K G]

/-- `R_F` is a bounded linear function of `W`. -/
theorem precompFamily_eq_flip (W : P → X →L[K] Y) (t : P) :
    precompFamily K F W t = (compL K X Y F).flip (W t) :=
  rfl

/-- `W` is `R_Y` evaluated at `id_Y`. -/
theorem eq_apply_precompFamily_self (W : P → X →L[K] Y) (t : P) :
    W t = ContinuousLinearMap.apply K (X →L[K] Y) (ContinuousLinearMap.id K Y)
      (precompFamily K Y W t) := by
  ext x; rfl

/-- `J_Y ∘ W(t)` is the flip of `R_K(t)`. -/
theorem bidualMap_comp_eq_flip (W : P → X →L[K] Y) (t : P) :
    (bidualMap K Y).comp (W t) =
      (flipₗᵢ K (StrongDual K Y) X K).toLinearIsometry.toContinuousLinearMap
        (precompFamily K K W t) := by
  ext x l; rfl

/-- `R_K(t)` is the flip of `J_Y ∘ W(t)`. -/
theorem precompFamily_scalar_eq_flip (W : P → X →L[K] Y) (t : P) :
    precompFamily K K W t =
      (flipₗᵢ K X (StrongDual K Y) K).toLinearIsometry.toContinuousLinearMap
        ((bidualMap K Y).comp (W t)) := by
  ext l x; rfl

/-- `R_{G*}(t)` is a bounded linear function of `R_K(t)`: `R_{G*}(t)(T) = (R_K(t) ∘ Tᶠ)ᶠ`. -/
theorem precompFamily_dual_eq (W : P → X →L[K] Y) (t : P) :
    precompFamily K (StrongDual K G) W t =
      ((sandwichL (flipₗᵢ K G X K).toLinearIsometry.toContinuousLinearMap
        (flipₗᵢ K Y G K).toLinearIsometry.toContinuousLinearMap).comp
        (compL K G (StrongDual K Y) (StrongDual K X))) (precompFamily K K W t) := by
  ext T x g; rfl

/-- `R_K(t)` is a bounded linear function of `R_{G*}(t)` once `φ g₀ ≠ 0`. -/
theorem precompFamily_scalar_eq_of_dual (W : P → X →L[K] Y) (t : P) (φ : StrongDual K G)
    (g₀ : G) (hg₀ : φ g₀ ≠ 0) :
    precompFamily K K W t =
      sandwichL (compL K X (StrongDual K G) K ((φ g₀)⁻¹ • ContinuousLinearMap.apply K K g₀))
        ((smulRightL K Y (StrongDual K G)).flip φ) (precompFamily K (StrongDual K G) W t) := by
  ext l x
  simp only [precompFamily_apply, coe_comp, Function.comp_apply, sandwichL_apply,
    compL_apply, flip_apply, smulRightL_apply_apply, smul_apply, apply_apply, smul_eq_mul,
    smulRight_apply]
  field_simp

/-- With a left inverse `P_Y` of `J_Y`, `W(t) = P_Y ∘ J_Y ∘ W(t)`. -/
theorem eq_of_bidualMap_leftInverse (W : P → X →L[K] Y)
    (PY : StrongDual K (StrongDual K Y) →L[K] Y)
    (hPY : PY.comp (bidualMap K Y) = ContinuousLinearMap.id K Y) (t : P) :
    W t = compL K X (StrongDual K (StrongDual K Y)) Y PY ((bidualMap K Y).comp (W t)) := by
  ext x
  simp [← ContinuousLinearMap.comp_apply PY (bidualMap K Y), hPY]

/-- With a left inverse `P_F` of `J_F`, `R_F(t)(T) = P_F ∘ R_{F**}(t)(J_F ∘ T)`. -/
theorem precompFamily_eq_of_bidualMap_leftInverse (W : P → X →L[K] Y)
    (PF : StrongDual K (StrongDual K F) →L[K] F)
    (hPF : PF.comp (bidualMap K F) = ContinuousLinearMap.id K F) (t : P) :
    precompFamily K F W t =
      sandwichL (compL K X (StrongDual K (StrongDual K F)) F PF)
        (compL K Y F (StrongDual K (StrongDual K F)) (bidualMap K F))
        (precompFamily K (StrongDual K (StrongDual K F)) W t) := by
  ext T x
  simp [← ContinuousLinearMap.comp_apply PF (bidualMap K F), hPF]

end Identities

section Tests

universe uF uG

variable [NormedAddCommGroup P] [NormedSpace K P] {U : Set P} (W : P → X →L[K] Y)

/-! ### Power-series analyticity -/

/-- Theorem 5.2(1), analytic: `W` analytic ⇒ every `R_F` analytic; `R_Y` analytic ⇒ `W`
analytic. -/
theorem part1_analytic :
    (AnalyticOnNhd K W U →
      ∀ (F : Type uF) [NormedAddCommGroup F] [NormedSpace K F],
        AnalyticOnNhd K (precompFamily K F W) U) ∧
    (AnalyticOnNhd K (precompFamily K Y W) U → AnalyticOnNhd K W U) :=
  ⟨fun hW F _ _ => analyticOnNhd_of_eq_clm _ (precompFamily_eq_flip F W) hW,
    fun h => analyticOnNhd_of_eq_clm _ (eq_apply_precompFamily_self W) h⟩

/-- `R_K` analytic ⇔ `J_Y ∘ W` analytic. -/
theorem analyticOnNhd_precompFamily_scalar_iff :
    AnalyticOnNhd K (precompFamily K K W) U ↔
      AnalyticOnNhd K (fun t => (bidualMap K Y).comp (W t)) U :=
  ⟨fun h => analyticOnNhd_of_eq_clm _ (bidualMap_comp_eq_flip W) h,
    fun h => analyticOnNhd_of_eq_clm _ (precompFamily_scalar_eq_flip W) h⟩

/-- `R_K` analytic ⇒ `R_{G*}` analytic. -/
theorem analyticOnNhd_precompFamily_dual (G : Type*) [NormedAddCommGroup G] [NormedSpace K G]
    (h : AnalyticOnNhd K (precompFamily K K W) U) :
    AnalyticOnNhd K (precompFamily K (StrongDual K G) W) U :=
  analyticOnNhd_of_eq_clm _ (precompFamily_dual_eq G W) h

/-- `R_{G*}` analytic ⇒ `R_K` analytic, for `G` with a nonzero continuous dual. -/
theorem analyticOnNhd_precompFamily_scalar_of_dual (G : Type*) [NormedAddCommGroup G]
    [NormedSpace K G] (hG : ∃ φ : StrongDual K G, φ ≠ 0)
    (h : AnalyticOnNhd K (precompFamily K (StrongDual K G) W) U) :
    AnalyticOnNhd K (precompFamily K K W) U := by
  obtain ⟨φ, hφ⟩ := hG
  obtain ⟨g₀, hg₀⟩ : ∃ g₀, φ g₀ ≠ 0 := by
    by_contra! hc
    exact hφ (ContinuousLinearMap.ext hc)
  exact analyticOnNhd_of_eq_clm _ (fun t => precompFamily_scalar_eq_of_dual G W t φ g₀ hg₀) h

/-- Theorem 5.2(2), analytic. -/
theorem part2_analytic :
    (AnalyticOnNhd K (precompFamily K K W) U ↔
      AnalyticOnNhd K (fun t => (bidualMap K Y).comp (W t)) U) ∧
    (AnalyticOnNhd K (precompFamily K K W) U →
      ∀ (G : Type uG) [NormedAddCommGroup G] [NormedSpace K G],
        AnalyticOnNhd K (precompFamily K (StrongDual K G) W) U) ∧
    (∀ (G : Type uG) [NormedAddCommGroup G] [NormedSpace K G],
      (∃ φ : StrongDual K G, φ ≠ 0) →
      AnalyticOnNhd K (precompFamily K (StrongDual K G) W) U →
      AnalyticOnNhd K (precompFamily K K W) U) :=
  ⟨analyticOnNhd_precompFamily_scalar_iff W,
    fun h G _ _ => analyticOnNhd_precompFamily_dual W G h,
    fun G _ _ hG h => analyticOnNhd_precompFamily_scalar_of_dual W G hG h⟩

/-- Theorem 5.2(3), analytic. -/
theorem part3_analytic :
    (∀ PY : StrongDual K (StrongDual K Y) →L[K] Y,
      PY.comp (bidualMap K Y) = ContinuousLinearMap.id K Y →
      AnalyticOnNhd K (precompFamily K K W) U → AnalyticOnNhd K W U) ∧
    (∀ (F : Type uF) [NormedAddCommGroup F] [NormedSpace K F]
      (PF : StrongDual K (StrongDual K F) →L[K] F),
      PF.comp (bidualMap K F) = ContinuousLinearMap.id K F →
      AnalyticOnNhd K (precompFamily K K W) U →
      AnalyticOnNhd K (precompFamily K F W) U) :=
  ⟨fun PY hPY h => analyticOnNhd_of_eq_clm _ (eq_of_bidualMap_leftInverse W PY hPY)
      ((analyticOnNhd_precompFamily_scalar_iff W).1 h),
    fun F _ _ PF hPF h => analyticOnNhd_of_eq_clm _
      (precompFamily_eq_of_bidualMap_leftInverse F W PF hPF)
      (analyticOnNhd_precompFamily_dual W (StrongDual K F) h)⟩

/-! ### The classes `C^n` -/

variable (n : ℕ∞)

/-- Theorem 5.2(1), `C^n`. -/
theorem part1_contDiff :
    (ContDiffOn K n W U →
      ∀ (F : Type uF) [NormedAddCommGroup F] [NormedSpace K F],
        ContDiffOn K n (precompFamily K F W) U) ∧
    (ContDiffOn K n (precompFamily K Y W) U → ContDiffOn K n W U) :=
  ⟨fun hW F _ _ => contDiffOn_of_eq_clm _ (precompFamily_eq_flip F W) hW,
    fun h => contDiffOn_of_eq_clm _ (eq_apply_precompFamily_self W) h⟩

/-- `R_K` is `C^n` ⇔ `J_Y ∘ W` is `C^n`. -/
theorem contDiffOn_precompFamily_scalar_iff :
    ContDiffOn K n (precompFamily K K W) U ↔
      ContDiffOn K n (fun t => (bidualMap K Y).comp (W t)) U :=
  ⟨fun h => contDiffOn_of_eq_clm _ (bidualMap_comp_eq_flip W) h,
    fun h => contDiffOn_of_eq_clm _ (precompFamily_scalar_eq_flip W) h⟩

/-- `R_K` is `C^n` ⇒ `R_{G*}` is `C^n`. -/
theorem contDiffOn_precompFamily_dual (G : Type*) [NormedAddCommGroup G] [NormedSpace K G]
    (h : ContDiffOn K n (precompFamily K K W) U) :
    ContDiffOn K n (precompFamily K (StrongDual K G) W) U :=
  contDiffOn_of_eq_clm _ (precompFamily_dual_eq G W) h

/-- `R_{G*}` is `C^n` ⇒ `R_K` is `C^n`, for `G` with a nonzero continuous dual. -/
theorem contDiffOn_precompFamily_scalar_of_dual (G : Type*) [NormedAddCommGroup G]
    [NormedSpace K G] (hG : ∃ φ : StrongDual K G, φ ≠ 0)
    (h : ContDiffOn K n (precompFamily K (StrongDual K G) W) U) :
    ContDiffOn K n (precompFamily K K W) U := by
  obtain ⟨φ, hφ⟩ := hG
  obtain ⟨g₀, hg₀⟩ : ∃ g₀, φ g₀ ≠ 0 := by
    by_contra! hc
    exact hφ (ContinuousLinearMap.ext hc)
  exact contDiffOn_of_eq_clm _ (fun t => precompFamily_scalar_eq_of_dual G W t φ g₀ hg₀) h

/-- Theorem 5.2(2), `C^n`. -/
theorem part2_contDiff :
    (ContDiffOn K n (precompFamily K K W) U ↔
      ContDiffOn K n (fun t => (bidualMap K Y).comp (W t)) U) ∧
    (ContDiffOn K n (precompFamily K K W) U →
      ∀ (G : Type uG) [NormedAddCommGroup G] [NormedSpace K G],
        ContDiffOn K n (precompFamily K (StrongDual K G) W) U) ∧
    (∀ (G : Type uG) [NormedAddCommGroup G] [NormedSpace K G],
      (∃ φ : StrongDual K G, φ ≠ 0) →
      ContDiffOn K n (precompFamily K (StrongDual K G) W) U →
      ContDiffOn K n (precompFamily K K W) U) :=
  ⟨contDiffOn_precompFamily_scalar_iff W n,
    fun h G _ _ => contDiffOn_precompFamily_dual W n G h,
    fun G _ _ hG h => contDiffOn_precompFamily_scalar_of_dual W n G hG h⟩

/-- Theorem 5.2(3), `C^n`. -/
theorem part3_contDiff :
    (∀ PY : StrongDual K (StrongDual K Y) →L[K] Y,
      PY.comp (bidualMap K Y) = ContinuousLinearMap.id K Y →
      ContDiffOn K n (precompFamily K K W) U → ContDiffOn K n W U) ∧
    (∀ (F : Type uF) [NormedAddCommGroup F] [NormedSpace K F]
      (PF : StrongDual K (StrongDual K F) →L[K] F),
      PF.comp (bidualMap K F) = ContinuousLinearMap.id K F →
      ContDiffOn K n (precompFamily K K W) U →
      ContDiffOn K n (precompFamily K F W) U) :=
  ⟨fun PY hPY h => contDiffOn_of_eq_clm _ (eq_of_bidualMap_leftInverse W PY hPY)
      ((contDiffOn_precompFamily_scalar_iff W n).1 h),
    fun F _ _ PF hPF h => contDiffOn_of_eq_clm _
      (precompFamily_eq_of_bidualMap_leftInverse F W PF hPF)
      (contDiffOn_precompFamily_dual W n (StrongDual K F) h)⟩

end Tests

end AlternatingAnalytic.DualTests
