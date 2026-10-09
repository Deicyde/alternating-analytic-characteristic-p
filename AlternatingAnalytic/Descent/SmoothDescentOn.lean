import Mathlib.Analysis.Calculus.ContDiff.LinearIsometry

/-!
# Smooth descent on an open set

Let `j : W →ₗᵢ[K] Z` be a linear isometry with closed range and `U ⊆ P` open. For `n : ℕ∞`, a map
`f : P → W` is `C^n` on `U` iff `j ∘ f` is (Lemma 3.2). This is the open-set version of
`LinearIsometry.comp_contDiff_iff`. Bump functions are not available over a general field, so the
induction on the order is redone on `U`, passing from `j` to `j.postcomp`, whose range is again
closed.
-/

open Set Function
open scoped ContDiff

namespace AlternatingAnalytic

/-- Finite-order smooth descent on an open set, with `W` and `Z` in a universe above that of `P`
so that the induction can pass to spaces of operators on `P`. -/
private theorem contDiffOn_of_comp_natCast.{uK, u, v} {K : Type uK} [NontriviallyNormedField K]
    {P : Type u} [NormedAddCommGroup P]
    [NormedSpace K P] {U : Set P} (hU : IsOpen U) (k : ℕ) :
    ∀ {W Z : Type (max u v)} [NormedAddCommGroup W] [NormedSpace K W] [NormedAddCommGroup Z]
      [NormedSpace K Z] (j : W →ₗᵢ[K] Z), IsClosed (range j) →
      ∀ {f : P → W}, ContDiffOn K k (j ∘ f) U → ContDiffOn K k f U := by
  induction k with
  | zero =>
    intro W Z _ _ _ _ j _ f h
    rw [Nat.cast_zero, contDiffOn_zero] at h ⊢
    exact (j.isometry.isEmbedding.continuousOn_iff).2 h
  | succ k ih =>
    intro W Z _ _ _ _ j hj f h
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hU] at h ⊢
    obtain ⟨hd, -, hfderiv⟩ := h
    have hf : ∀ x ∈ U, DifferentiableAt K f x := fun x hx ↦
      (j.exists_hasFDerivAt_of_comp hj
        ((hd x hx).differentiableAt (hU.mem_nhds hx)).hasFDerivAt).choose_spec.1.differentiableAt
    have hchain : EqOn (j.postcomp ∘ fderiv K f) (fderiv K (j ∘ f)) U := fun x hx ↦
      ((j.toContinuousLinearMap.hasFDerivAt.comp x (hf x hx).hasFDerivAt).fderiv).symm
    exact ⟨fun x hx ↦ (hf x hx).differentiableWithinAt, fun h ↦ absurd h (by simp),
      ih _ (j.isClosed_range_postcomp hj) (hfderiv.congr hchain)⟩

/-- Lemma 3.2: on an open set, `f` is `C^n` (`n ≤ ∞`) iff `j ∘ f` is, for a linear isometry `j`
with closed range. -/
theorem contDiffOn_iff_comp_linearIsometry.{uK, uP, uW, uZ} {K : Type uK}
    [NontriviallyNormedField K] {P : Type uP} [NormedAddCommGroup P]
    [NormedSpace K P] {W : Type uW} [NormedAddCommGroup W] [NormedSpace K W]
    {Z : Type uZ} [NormedAddCommGroup Z] [NormedSpace K Z]
    (j : W →ₗᵢ[K] Z) (hj : IsClosed (range j)) {U : Set P} (hU : IsOpen U) (f : P → W)
    (n : ℕ∞) : ContDiffOn K n f U ↔ ContDiffOn K n (j ∘ f) U := by
  refine ⟨fun h ↦ j.toContinuousLinearMap.contDiff.comp_contDiffOn h, fun h ↦ ?_⟩
  rw [contDiffOn_iff_forall_nat_le] at h ⊢
  intro k hk
  let eW : ULift.{max uP uZ, uW} W ≃ₗᵢ[K] W := LinearIsometryEquiv.ulift K W
  let eZ : ULift.{max uP uW, uZ} Z ≃ₗᵢ[K] Z := LinearIsometryEquiv.ulift K Z
  let Ψ := eZ.symm.toLinearIsometry.comp (j.comp eW.toLinearIsometry)
  have hΨ : IsClosed (range Ψ) := by
    rw [LinearIsometry.coe_comp, LinearIsometry.coe_comp,
      LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.coe_toLinearIsometry,
      range_comp, eW.surjective.range_comp]
    exact eZ.symm.toHomeomorph.isClosed_image.2 hj
  have := contDiffOn_of_comp_natCast.{uK, uP, max uW uZ} hU k Ψ hΨ (f := eW.symm ∘ f) <| by
    simpa [Ψ, comp_def] using
      eZ.symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn (h k hk)
  simpa [comp_def] using eW.toContinuousLinearEquiv.contDiff.comp_contDiffOn this

end AlternatingAnalytic
