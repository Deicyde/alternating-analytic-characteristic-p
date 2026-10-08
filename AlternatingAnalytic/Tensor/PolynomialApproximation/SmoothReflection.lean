/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
import Mathlib.Analysis.Calculus.ContDiff.LinearIsometry

/-!
# Smoothness reflects along a closed isometric embedding on open sets

The fork lemma `LinearIsometry.comp_contDiff_iff` reflects global `C^n`-smoothness along a
linear isometry with closed range. This file gives the version on an open set: if `Φ ∘ f` is
`C^n` on an open set `s`, then so is `f`. The proof is the same induction on the order, with
`contDiffOn_succ_iff_fderiv_of_isOpen` in place of `contDiff_succ_iff_fderiv`; it passes from
`Φ` to `Φ.postcomp`, so all three spaces live in one universe.
-/

open Set Function Filter
open scoped ContDiff

namespace AlternatingAnalytic.PolynomialApproximation

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- Finite orders of the open-set reflection, by induction on the order. -/
theorem contDiffOn_of_comp_linearIsometry_natCast.{u} (k : ℕ) :
    ∀ {E F G : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
      [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G] (Φ : E →ₗᵢ[𝕜] F),
      IsClosed (range Φ) → ∀ {f : G → E} {s : Set G}, IsOpen s →
        ContDiffOn 𝕜 k (Φ ∘ f) s → ContDiffOn 𝕜 k f s := by
  induction k with
  | zero =>
    intro E F G _ _ _ _ _ _ Φ _ f s _ h
    rw [Nat.cast_zero, contDiffOn_zero] at h ⊢
    exact Φ.isometry.isEmbedding.continuousOn_iff.2 h
  | succ k ih =>
    intro E F G _ _ _ _ _ _ Φ hΦ f s hs h
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hs] at h ⊢
    obtain ⟨hd, -, hfderiv⟩ := h
    have hf : ∀ x ∈ s, DifferentiableAt 𝕜 f x := fun x hx ↦
      (Φ.exists_hasFDerivAt_of_comp hΦ
        ((hd x hx).differentiableAt (hs.mem_nhds hx)).hasFDerivAt).choose_spec.1.differentiableAt
    have hchain : EqOn (fderiv 𝕜 (Φ ∘ f)) (Φ.postcomp ∘ fderiv 𝕜 f) s := fun x hx ↦
      (Φ.toContinuousLinearMap.hasFDerivAt.comp x (hf x hx).hasFDerivAt).fderiv
    exact ⟨fun x hx ↦ (hf x hx).differentiableWithinAt, fun h ↦ absurd h (by simp),
      ih _ (Φ.isClosed_range_postcomp hΦ) hs (hfderiv.congr fun x hx ↦ (hchain hx).symm)⟩

/-- Postcomposition with a linear isometry with closed range reflects `C^n`-smoothness on an
open set, for `n : ℕ∞`. -/
theorem contDiffOn_of_comp_linearIsometry.{u} {E F G : Type u} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G]
    [NormedSpace 𝕜 G] (Φ : E →ₗᵢ[𝕜] F) (hΦ : IsClosed (range Φ)) {n : ℕ∞} {f : G → E}
    {s : Set G} (hs : IsOpen s) (h : ContDiffOn 𝕜 n (Φ ∘ f) s) : ContDiffOn 𝕜 n f s := by
  rw [contDiffOn_iff_forall_nat_le] at h ⊢
  exact fun k hk ↦ contDiffOn_of_comp_linearIsometry_natCast k Φ hΦ hs (h k hk)

/-- A map into a closed subspace is `C^n` on an open set as soon as its composite with the
inclusion is. -/
theorem contDiffOn_of_subtype.{u} {F G : Type u} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] (W : Submodule 𝕜 F) (hW : IsClosed (W : Set F))
    {n : ℕ∞} {f : G → W} {s : Set G} (hs : IsOpen s)
    (h : ContDiffOn 𝕜 n (fun x ↦ (f x : F)) s) : ContDiffOn 𝕜 n f s :=
  contDiffOn_of_comp_linearIsometry W.subtypeₗᵢ (by simpa using hW) hs h

end AlternatingAnalytic.PolynomialApproximation
