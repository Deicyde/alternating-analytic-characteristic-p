/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
import Mathlib.Analysis.Calculus.ContDiff.ContinuousAlternatingMap
import Mathlib.Analysis.Analytic.CPolynomial
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Data.Nat.Prime.Factorial

/-!
# Precomposition on continuous alternating maps when `(card ι)!` is invertible

Source: round24/charp/lean/FactorialInvertible.lean, integrated on 2026-09-23.
Provenance and verification: planning/charp-paper/planning/integration-manifest.json.

Alternatization `A μ = ∑_σ sgn σ • (μ ∘ σ)` is a bounded linear map from continuous multilinear
maps to continuous alternating maps, of norm at most `(Fintype.card ι)!`
(`ContinuousMultilinearMap.norm_alternatization_le`,
`ContinuousMultilinearMap.alternatizationCLM`), and it multiplies an already alternating map by
`(Fintype.card ι)!`. Hence, as soon as `((Fintype.card ι)! : 𝕜) ≠ 0`, the normalised
alternatization `altProj = ((Fintype.card ι)! : 𝕜)⁻¹ • A` is a continuous linear **retraction**
of the inclusion of alternating maps into multilinear maps, and precomposition
`f ↦ (m ↦ m ∘ (f, …, f))` is continuously polynomial, hence `C^n` for every `n : WithTop ℕ∞` —
including the analytic case `n = ω`.

Main results:

* `ContinuousAlternatingMap.cpolynomialAt_compContinuousLinearMapCLM`
* `ContinuousAlternatingMap.contDiff_compContinuousLinearMapCLM_of_factorial_ne_zero`
* corollaries under `[Invertible ((Fintype.card ι)! : 𝕜)]`, under `[CharP 𝕜 p]` with
  `¬ p ∣ (Fintype.card ι)!`, and under `[CharP 𝕜 p]` with `p` prime and `Fintype.card ι < p`.

## Scope

The hypothesis `((Fintype.card ι)! : 𝕜) ≠ 0` means characteristic `0`, or characteristic `p`
prime with `p > Fintype.card ι`. It is **not** "characteristic `≠ 2`": for `Fintype.card ι = 3`
and characteristic `3` it does not apply. This module proves only the factorial-invertible
positive direction; no negative result or complete-target counterexample is asserted here.

## Relation to mathlib#43338

Sébastien Gouëzel's PR #43338 proves the same continuous-polynomiality under `[CharZero 𝕜]`.
His argument only ever uses `((Fintype.card ι)! : 𝕜) ≠ 0` (it divides by that one scalar), so it
generalises verbatim; the polynomial core below,
`ContinuousAlternatingMap.cpolynomialAt_nsmul_compContinuousLinearMapCLM`, is his argument, and
only the final normalisation changes. When transcribing his script in the PR #43548 checkout it
was necessary to supply explicit type arguments to `ContinuousLinearMap.comp_cpolynomialAt`
(see the `(𝕜 := _) (E := _) (F := _) (G := _)` annotations below): the elaborator otherwise picks
the wrong `ContinuousLinearMap` module instance — an instance-diamond workaround recorded in
research-notes §11.1.
-/

open scoped Nat ContDiff
open ContinuousMultilinearMap

namespace ContinuousMultilinearMap

variable {𝕜 ι E F : Type*} [NontriviallyNormedField 𝕜] [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Alternatization increases the norm by at most `(Fintype.card ι)!`. -/
theorem norm_alternatization_le (f : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F) :
    ‖alternatization f‖ ≤ ((Fintype.card ι)! : ℝ) * ‖f‖ := by
  rw [← ContinuousAlternatingMap.norm_toContinuousMultilinearMap,
    alternatization_apply_toContinuousMultilinearMap]
  refine le_trans (norm_sum_le _ _) ?_
  have h : ∀ σ : Equiv.Perm ι, ‖(Equiv.Perm.sign σ : ℤ) • f.domDomCongr σ‖ ≤ ‖f‖ := by
    intro σ
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h, norm_domDomCongr]
  calc ∑ σ : Equiv.Perm ι, ‖(Equiv.Perm.sign σ : ℤ) • f.domDomCongr σ‖
      ≤ ∑ _σ : Equiv.Perm ι, ‖f‖ := Finset.sum_le_sum fun σ _ ↦ h σ
    _ = ((Fintype.card ι)! : ℝ) * ‖f‖ := by simp [Finset.card_univ, Fintype.card_perm]

variable (𝕜 E F) in
/-- Alternatization, as a continuous linear map from continuous multilinear maps to continuous
alternating maps. Its operator norm is at most `(Fintype.card ι)!`. -/
noncomputable def alternatizationCLM :
    ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F →L[𝕜] (E [⋀^ι]→L[𝕜] F) :=
  LinearMap.mkContinuous
    { toFun := alternatization
      map_add' := map_add _
      map_smul' := by
        intro c f
        ext v
        simp only [RingHom.id_apply, ContinuousAlternatingMap.smul_apply,
          alternatization_apply_apply, smul_apply, Finset.smul_sum]
        exact Finset.sum_congr rfl fun σ _ ↦ smul_comm _ _ _ }
    ((Fintype.card ι)! : ℝ) (fun f ↦ norm_alternatization_le f)

@[simp] theorem alternatizationCLM_apply (f : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F) :
    alternatizationCLM 𝕜 E F f = alternatization f := rfl

theorem norm_alternatizationCLM_le :
    ‖alternatizationCLM (ι := ι) 𝕜 E F‖ ≤ ((Fintype.card ι)! : ℝ) :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

/-- Alternatizing an already alternating map multiplies it by `(Fintype.card ι)!`. -/
theorem alternatization_toContinuousMultilinearMap (a : E [⋀^ι]→L[𝕜] F) :
    alternatization a.toContinuousMultilinearMap = (Fintype.card ι)! • a := by
  ext v
  have h : MultilinearMap.alternatization a.toAlternatingMap.toMultilinearMap v =
      ((Fintype.card ι)! • a.toAlternatingMap) v := by
    rw [AlternatingMap.coe_alternatization a.toAlternatingMap]
  simpa only [MultilinearMap.alternatization_apply, alternatization_apply_apply] using! h

/-- Scalar form of `ContinuousMultilinearMap.alternatization_toContinuousMultilinearMap`. -/
theorem alternatizationCLM_toContinuousMultilinearMap (a : E [⋀^ι]→L[𝕜] F) :
    alternatizationCLM 𝕜 E F a.toContinuousMultilinearMap = (((Fintype.card ι)! : 𝕜)) • a := by
  rw [alternatizationCLM_apply, alternatization_toContinuousMultilinearMap,
    Nat.cast_smul_eq_nsmul]

end ContinuousMultilinearMap

namespace ContinuousAlternatingMap

open ContinuousMultilinearMap

variable {𝕜 ι E E' F : Type*} [NontriviallyNormedField 𝕜] [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (𝕜 E F) in
/-- The normalised alternatization: a continuous linear retraction of the inclusion of continuous
alternating maps into continuous multilinear maps, available whenever `(Fintype.card ι)!` is
invertible in `𝕜`. -/
noncomputable def altProj :
    ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F →L[𝕜] (E [⋀^ι]→L[𝕜] F) :=
  ((Fintype.card ι)! : 𝕜)⁻¹ • alternatizationCLM 𝕜 E F

/-- `ContinuousAlternatingMap.altProj` is a retraction of the inclusion. -/
theorem altProj_toContinuousMultilinearMap (h : ((Fintype.card ι)! : 𝕜) ≠ 0)
    (a : E [⋀^ι]→L[𝕜] F) : altProj 𝕜 E F a.toContinuousMultilinearMap = a := by
  rw [altProj, _root_.smul_apply, alternatizationCLM_toContinuousMultilinearMap,
    smul_smul, inv_mul_cancel₀ h, one_smul]

/-- The continuous linear map `u ↦ alternatization ∘ u ∘ (inclusion of alternating maps)`. -/
noncomputable def compAlternatizationCLM :
    (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E') F →L[𝕜]
        ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F) →L[𝕜]
      ((E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)) :=
  (ContinuousLinearMap.compL 𝕜 (E' [⋀^ι]→L[𝕜] F)
      (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F) (E [⋀^ι]→L[𝕜] F)
      (alternatizationCLM 𝕜 E F)).comp
    ((ContinuousLinearMap.compL 𝕜 (E' [⋀^ι]→L[𝕜] F)
      (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E') F)
      (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F)).flip (toContinuousMultilinearMapCLM 𝕜))

theorem compAlternatizationCLM_apply
    (u : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E') F →L[𝕜]
      ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F) (m : E' [⋀^ι]→L[𝕜] F) :
    compAlternatizationCLM (𝕜 := 𝕜) (ι := ι) (E := E) (E' := E') (F := F) u m =
      alternatization (u m.toContinuousMultilinearMap) := by
  simp [compAlternatizationCLM]

/-- `(Fintype.card ι)!` times precomposition on continuous alternating maps is continuously
polynomial. This is the argument of mathlib#43338 (Gouëzel), with no hypothesis on `𝕜`. -/
theorem cpolynomialAt_nsmul_compContinuousLinearMapCLM (f₀ : E →L[𝕜] E') :
    CPolynomialAt 𝕜 ((Fintype.card ι)! •
      compContinuousLinearMapCLM :
        (E →L[𝕜] E') → (E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)) f₀ := by
  classical
  set B : ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ (E →L[𝕜] E'))
      ((ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E') F)
        →L[𝕜] (ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F)) :=
    compContinuousLinearMapContinuousMultilinear _ _ _ _ with hB
  have key : ((Fintype.card ι)! • compContinuousLinearMapCLM :
        (E →L[𝕜] E') → (E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)) =
      fun f ↦ compAlternatizationCLM (𝕜 := 𝕜) (ι := ι) (E := E) (E' := E') (F := F)
        (B (fun _ ↦ f)) := by
    ext f m : 2
    simp only [Pi.smul_apply, _root_.smul_apply, compContinuousLinearMapCLM_apply,
      ← alternatization_toContinuousMultilinearMap, compAlternatizationCLM_apply]
    rfl
  rw [key]
  have h3 : CPolynomialAt 𝕜 (fun f : E →L[𝕜] E' ↦ B (fun _ : ι ↦ f)) f₀ :=
    CPolynomialAt.comp (g := ⇑B) (f := fun f : E →L[𝕜] E' ↦ (fun _ : ι ↦ f))
      (ContinuousMultilinearMap.cpolynomialAt _)
      (ContinuousLinearMap.cpolynomialAt
        (ContinuousLinearMap.pi fun _ : ι ↦ ContinuousLinearMap.id 𝕜 (E →L[𝕜] E')) f₀)
  -- the explicit type arguments below work around a `ContinuousLinearMap` instance diamond
  exact ContinuousLinearMap.comp_cpolynomialAt (𝕜 := 𝕜) (E := E →L[𝕜] E')
    (F := ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E') F →L[𝕜]
      ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F)
    (G := (E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F))
    (compAlternatizationCLM (𝕜 := 𝕜) (ι := ι) (E := E) (E' := E') (F := F)) h3

private theorem cpolynomialAt_const_smul {X Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] {f : X → Y} {x : X}
    (hf : CPolynomialAt 𝕜 f x) (c : 𝕜) : CPolynomialAt 𝕜 (c • f) x :=
  ContinuousLinearMap.comp_cpolynomialAt (ContinuousLinearMap.lsmul 𝕜 𝕜 c) hf

/-- **F1.** If `(Fintype.card ι)!` is invertible in `𝕜` — characteristic `0`, or characteristic
`p` prime with `p > Fintype.card ι` — then precomposition on spaces of continuous alternating
maps is continuously polynomial. No completeness, arbitrary normed spaces. -/
theorem cpolynomialAt_compContinuousLinearMapCLM (h : ((Fintype.card ι)! : 𝕜) ≠ 0)
    (f₀ : E →L[𝕜] E') :
    CPolynomialAt 𝕜 (compContinuousLinearMapCLM :
      (E →L[𝕜] E') → (E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)) f₀ := by
  have key : (compContinuousLinearMapCLM :
      (E →L[𝕜] E') → (E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)) =
      ((Fintype.card ι)! : 𝕜)⁻¹ • ((Fintype.card ι)! • compContinuousLinearMapCLM) := by
    rw [← Nat.cast_smul_eq_nsmul 𝕜, smul_smul, inv_mul_cancel₀ h, one_smul]
  rw [key]
  exact cpolynomialAt_const_smul (cpolynomialAt_nsmul_compContinuousLinearMapCLM f₀) _

theorem cpolynomialOn_compContinuousLinearMapCLM (h : ((Fintype.card ι)! : 𝕜) ≠ 0)
    (s : Set (E →L[𝕜] E')) :
    CPolynomialOn 𝕜 (compContinuousLinearMapCLM :
      (E →L[𝕜] E') → (E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)) s :=
  fun f _ ↦ cpolynomialAt_compContinuousLinearMapCLM h f

theorem analyticOnNhd_compContinuousLinearMapCLM (h : ((Fintype.card ι)! : 𝕜) ≠ 0)
    (s : Set (E →L[𝕜] E')) :
    AnalyticOnNhd 𝕜 (compContinuousLinearMapCLM :
      (E →L[𝕜] E') → (E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)) s :=
  (cpolynomialOn_compContinuousLinearMapCLM h s).analyticOnNhd

/-- **F1, smoothness form.** With `(Fintype.card ι)!` invertible in `𝕜`, precomposition on
continuous alternating maps is `C^n` for every `n : WithTop ℕ∞`, including the analytic case
`n = ω`.

Some hypothesis is needed at `n = ω`: the statement is false in characteristic `2` over a
complete, non-spherically-complete field. -/
theorem contDiff_compContinuousLinearMapCLM_of_factorial_ne_zero
    (h : ((Fintype.card ι)! : 𝕜) ≠ 0) {n : WithTop ℕ∞} :
    ContDiff 𝕜 n (compContinuousLinearMapCLM :
      (E →L[𝕜] E') → (E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)) :=
  contDiff_iff_contDiffAt.2 fun f₀ ↦ (cpolynomialAt_compContinuousLinearMapCLM h f₀).contDiffAt

/-- `Invertible`-flavoured restatement of F1. -/
theorem contDiff_compContinuousLinearMapCLM_of_invertible
    [Invertible ((Fintype.card ι)! : 𝕜)] {n : WithTop ℕ∞} :
    ContDiff 𝕜 n (compContinuousLinearMapCLM :
      (E →L[𝕜] E') → (E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)) :=
  contDiff_compContinuousLinearMapCLM_of_factorial_ne_zero (isUnit_of_invertible _).ne_zero

/-- Characteristic form of F1: if the characteristic does not divide `(Fintype.card ι)!`, then
precomposition is `C^n` for every `n`, including `n = ω`. -/
theorem contDiff_compContinuousLinearMapCLM_of_charP (p : ℕ) [CharP 𝕜 p]
    (hp : ¬ p ∣ (Fintype.card ι)!) {n : WithTop ℕ∞} :
    ContDiff 𝕜 n (compContinuousLinearMapCLM :
      (E →L[𝕜] E') → (E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)) :=
  contDiff_compContinuousLinearMapCLM_of_factorial_ne_zero
    (by rw [Ne, CharP.cast_eq_zero_iff 𝕜 p]; exact hp)

/-- In characteristic `p` prime with `p > Fintype.card ι` (for instance `Fintype.card ι = 2` and
`p ≥ 3`), precomposition on continuous alternating maps is analytic. -/
theorem contDiff_compContinuousLinearMapCLM_of_card_lt_charP (p : ℕ) [hp : Fact p.Prime]
    [CharP 𝕜 p] (h : Fintype.card ι < p) {n : WithTop ℕ∞} :
    ContDiff 𝕜 n (compContinuousLinearMapCLM :
      (E →L[𝕜] E') → (E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)) :=
  contDiff_compContinuousLinearMapCLM_of_charP p
    (fun hd ↦ absurd ((Nat.Prime.dvd_factorial hp.out).1 hd) (not_le.2 h))

end ContinuousAlternatingMap
