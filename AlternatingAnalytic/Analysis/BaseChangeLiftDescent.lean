/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
import AlternatingAnalytic.Analysis.BaseChangeOperators
import AlternatingAnalytic.Analysis.BaseChangeAlternatingForms
import AlternatingAnalytic.Analysis.LiftCriterion

/-!
# Descent of a bounded lift through completed base change

A bounded multilinear lift of the pullback over the completed base change gives one over
`K` of no larger norm; hence failure of analyticity over `K` persists after base change
(Proposition D.9). The proof combines base change of operators and of alternating forms
with a contracting retraction of the completed base change of `F` onto `F`.
-/

namespace AlternatingAnalytic

universe u

variable (K : Type*) (E F L : Type u) [NontriviallyNormedField K]
  [NormedAddCommGroup E] [NormedSpace K E] [NormedAddCommGroup F] [NormedSpace K F]
  [NontriviallyNormedField L] [NormedAlgebra K L] [CompleteSpace K]
  [IsUltrametricDist K] [SphericallyCompleteSpace K] [IsUltrametricDist L]

/-- The operator seminorm on the lift space, named to help instance search. -/
noncomputable local instance liftSeminormedAddCommGroup (n : ℕ) :
    SeminormedAddCommGroup ((E →L[K] E) [×n]→L[K]
      ((E [⋀^Fin n]→L[K] F) →L[K] (E [⋀^Fin n]→L[K] F))) :=
  ContinuousMultilinearMap.seminormedAddCommGroup (𝕜 := K)
    (E := fun _ : Fin n => E →L[K] E)
    (G := (E [⋀^Fin n]→L[K] F) →L[K] (E [⋀^Fin n]→L[K] F))

/-- The operator norm on the lift space. -/
noncomputable local instance liftNorm (n : ℕ) :
    Norm ((E →L[K] E) [×n]→L[K]
      ((E [⋀^Fin n]→L[K] F) →L[K] (E [⋀^Fin n]→L[K] F))) :=
  ContinuousMultilinearMap.hasOpNorm (𝕜 := K)
    (E := fun _ : Fin n => E →L[K] E)
    (G := (E [⋀^Fin n]→L[K] F) →L[K] (E [⋀^Fin n]→L[K] F))

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
omit [CompleteSpace K] [IsUltrametricDist K] [SphericallyCompleteSpace K] in
/-- The multilinear operator-norm bound on the lift space. -/
theorem norm_lift_apply_le (n : ℕ)
    (P : (E →L[K] E) [×n]→L[K]
      ((E [⋀^Fin n]→L[K] F) →L[K] (E [⋀^Fin n]→L[K] F)))
    (f : Fin n → E →L[K] E) :
    ‖P f‖ ≤ ‖P‖ * ∏ i, ‖f i‖ := by
  let S : Set ℝ := {c | 0 ≤ c ∧ ∀ fs : Fin n → E →L[K] E,
    ‖P fs‖ ≤ c * ∏ i, ‖fs i‖}
  have hclosed : IsClosed S := by
    dsimp only [S]
    simp only [Set.ofPred_and, Set.ofPred_forall]
    exact isClosed_Ici.inter (isClosed_iInter fun fs =>
      isClosed_le continuous_const (by fun_prop))
  have hnonempty : S.Nonempty := by
    obtain ⟨C, hC, hbound⟩ := ContinuousMultilinearMap.bound (𝕜 := K)
      (E := fun _ : Fin n => E →L[K] E)
      (G := (E [⋀^Fin n]→L[K] F) →L[K] (E [⋀^Fin n]→L[K] F)) P
    exact ⟨C, hC.le, hbound⟩
  have hbelow : BddBelow S := ⟨0, fun _ h => h.1⟩
  change ‖P f‖ ≤ sInf S * ∏ i, ‖f i‖
  exact (hclosed.isLeast_csInf hnonempty hbelow).1.2 f

/-- Restrict an `L`-alternating form to `E` and compose with a `K`-linear map `r`. -/
noncomputable def baseChangeFormRestriction
    (r : CompletedBaseChange K F L →L[K] F) (n : ℕ) :
    (CompletedBaseChange K E L [⋀^Fin n]→L[L] CompletedBaseChange K F L) →L[K]
      (E [⋀^Fin n]→L[K] F) :=
  (ContinuousLinearMap.compContinuousAlternatingMapCLM K E
    (CompletedBaseChange K F L) F (Fin n) r).comp
    ((ContinuousAlternatingMap.compContinuousLinearMapCLM
      (completedBaseChangeEmbedding K E L).toContinuousLinearMap).comp
      (ContinuousAlternatingMap.restrictScalarsLI K).toContinuousLinearMap)

@[simp]
theorem baseChangeFormRestriction_apply
    (r : CompletedBaseChange K F L →L[K] F) (n : ℕ)
    (m : CompletedBaseChange K E L [⋀^Fin n]→L[L] CompletedBaseChange K F L)
    (x : Fin n → E) :
    baseChangeFormRestriction K E F L r n m x =
      r (m (fun i => completedBaseChangeEmbedding K E L (x i))) := rfl

theorem norm_baseChangeFormRestriction_apply_le
    (r : CompletedBaseChange K F L →L[K] F) (n : ℕ)
    (m : CompletedBaseChange K E L [⋀^Fin n]→L[L] CompletedBaseChange K F L) :
    ‖baseChangeFormRestriction K E F L r n m‖ ≤ ‖r‖ * ‖m‖ := by
  change ‖r.compContinuousAlternatingMap
    ((m.restrictScalars K).compContinuousLinearMap
      (completedBaseChangeEmbedding K E L).toContinuousLinearMap)‖ ≤ ‖r‖ * ‖m‖
  apply (r.norm_compContinuousAlternatingMap_le _).trans
  apply mul_le_mul_of_nonneg_left ?_ (norm_nonneg r)
  exact (m.restrictScalars K).toContinuousMultilinearMap.norm_compContinuous_linearIsometry_le
    (fun _ => completedBaseChangeEmbedding K E L)

theorem norm_baseChangeFormRestriction_le
    (r : CompletedBaseChange K F L →L[K] F) (n : ℕ) :
    ‖baseChangeFormRestriction K E F L r n‖ ≤ ‖r‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg r)
    (norm_baseChangeFormRestriction_apply_le K E F L r n)

/-- `T ↦ (m ↦ restriction of T (m_{K'}))`, from operators over `L` to operators over `K`. -/
noncomputable def baseChangeLiftRestriction
    (r : CompletedBaseChange K F L →L[K] F) (n : ℕ) :
    ((CompletedBaseChange K E L [⋀^Fin n]→L[L] CompletedBaseChange K F L) →L[L]
      (CompletedBaseChange K E L [⋀^Fin n]→L[L] CompletedBaseChange K F L)) →L[K]
      ((E [⋀^Fin n]→L[K] F) →L[K] (E [⋀^Fin n]→L[K] F)) :=
  (ContinuousLinearMap.compL K (E [⋀^Fin n]→L[K] F)
      (CompletedBaseChange K E L [⋀^Fin n]→L[L] CompletedBaseChange K F L)
      (E [⋀^Fin n]→L[K] F) (baseChangeFormRestriction K E F L r n)).comp
    (((ContinuousLinearMap.compL K (E [⋀^Fin n]→L[K] F)
      (CompletedBaseChange K E L [⋀^Fin n]→L[L] CompletedBaseChange K F L)
      (CompletedBaseChange K E L [⋀^Fin n]→L[L] CompletedBaseChange K F L)).flip
        (baseChangeAlternatingForms K E F L n)).comp
      (ContinuousLinearMap.restrictScalarsIsometry L
        (CompletedBaseChange K E L [⋀^Fin n]→L[L] CompletedBaseChange K F L)
        (CompletedBaseChange K E L [⋀^Fin n]→L[L] CompletedBaseChange K F L)
        K K).toContinuousLinearMap)

@[simp]
theorem baseChangeLiftRestriction_apply
    (r : CompletedBaseChange K F L →L[K] F) (n : ℕ)
    (T : (CompletedBaseChange K E L [⋀^Fin n]→L[L] CompletedBaseChange K F L) →L[L]
      (CompletedBaseChange K E L [⋀^Fin n]→L[L] CompletedBaseChange K F L))
    (m : E [⋀^Fin n]→L[K] F) (x : Fin n → E) :
    baseChangeLiftRestriction K E F L r n T m x =
      r (T (baseChangeAlternatingForms K E F L n m)
        (fun i => completedBaseChangeEmbedding K E L (x i))) := rfl

theorem norm_baseChangeLiftRestriction_apply_le
    (r : CompletedBaseChange K F L →L[K] F) (n : ℕ)
    (T : (CompletedBaseChange K E L [⋀^Fin n]→L[L] CompletedBaseChange K F L) →L[L]
      (CompletedBaseChange K E L [⋀^Fin n]→L[L] CompletedBaseChange K F L)) :
    ‖baseChangeLiftRestriction K E F L r n T‖ ≤ ‖r‖ * ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg r) (norm_nonneg T))
  intro m
  change ‖baseChangeFormRestriction K E F L r n
    (T (baseChangeAlternatingForms K E F L n m))‖ ≤ (‖r‖ * ‖T‖) * ‖m‖
  calc
    _ ≤ ‖r‖ * ‖T (baseChangeAlternatingForms K E F L n m)‖ :=
      norm_baseChangeFormRestriction_apply_le K E F L r n _
    _ ≤ ‖r‖ * (‖T‖ * ‖baseChangeAlternatingForms K E F L n m‖) :=
      mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg r)
    _ ≤ ‖r‖ * (‖T‖ * ‖m‖) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (norm_baseChangeAlternatingForms_apply_le K E F L n m)
        (norm_nonneg T)) (norm_nonneg r)
    _ = (‖r‖ * ‖T‖) * ‖m‖ := (mul_assoc _ _ _).symm

/-- The descended lift `(f_i) ↦ (m ↦ r ∘ P((f_i)_{K'})(m_{K'}) ∘ ι)` (Proposition D.9). -/
noncomputable def baseChangeLiftDescent
    (r : CompletedBaseChange K F L →L[K] F) (n : ℕ)
    (P : (CompletedBaseChange K E L →L[L] CompletedBaseChange K E L) [×n]→L[L]
      ((CompletedBaseChange K E L [⋀^Fin n]→L[L] CompletedBaseChange K F L) →L[L]
        (CompletedBaseChange K E L [⋀^Fin n]→L[L] CompletedBaseChange K F L))) :
    (E →L[K] E) [×n]→L[K] ((E [⋀^Fin n]→L[K] F) →L[K] (E [⋀^Fin n]→L[K] F)) :=
  (baseChangeLiftRestriction K E F L r n).compContinuousMultilinearMap
    ((P.restrictScalars K).compContinuousLinearMap fun _ => baseChangeOperators K E L)

@[simp]
theorem baseChangeLiftDescent_apply
    (r : CompletedBaseChange K F L →L[K] F) (n : ℕ)
    (P : (CompletedBaseChange K E L →L[L] CompletedBaseChange K E L) [×n]→L[L]
      ((CompletedBaseChange K E L [⋀^Fin n]→L[L] CompletedBaseChange K F L) →L[L]
        (CompletedBaseChange K E L [⋀^Fin n]→L[L] CompletedBaseChange K F L)))
    (f : Fin n → E →L[K] E) (m : E [⋀^Fin n]→L[K] F) (x : Fin n → E) :
    baseChangeLiftDescent K E F L r n P f m x =
      r (P (fun i => completedBaseChangeOperator K E L (f i))
        (baseChangeAlternatingForms K E F L n m)
        (fun i => completedBaseChangeEmbedding K E L (x i))) := rfl

theorem norm_baseChangeLiftDescent_le
    (r : CompletedBaseChange K F L →L[K] F) (n : ℕ)
    (P : (CompletedBaseChange K E L →L[L] CompletedBaseChange K E L) [×n]→L[L]
      ((CompletedBaseChange K E L [⋀^Fin n]→L[L] CompletedBaseChange K F L) →L[L]
        (CompletedBaseChange K E L [⋀^Fin n]→L[L] CompletedBaseChange K F L))) :
    ‖baseChangeLiftDescent K E F L r n P‖ ≤ ‖r‖ * ‖P‖ := by
  apply ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg (norm_nonneg r) (norm_nonneg P))
  intro f
  change ‖baseChangeLiftRestriction K E F L r n
    (P (fun i => completedBaseChangeOperator K E L (f i)))‖ ≤
      (‖r‖ * ‖P‖) * ∏ i, ‖f i‖
  calc
    _ ≤ ‖r‖ * ‖P (fun i => completedBaseChangeOperator K E L (f i))‖ :=
      norm_baseChangeLiftRestriction_apply_le K E F L r n _
    _ ≤ ‖r‖ * (‖P‖ * ∏ i, ‖completedBaseChangeOperator K E L (f i)‖) :=
      mul_le_mul_of_nonneg_left
        (norm_lift_apply_le L (CompletedBaseChange K E L) (CompletedBaseChange K F L)
          n P (fun i => completedBaseChangeOperator K E L (f i))) (norm_nonneg r)
    _ ≤ ‖r‖ * (‖P‖ * ∏ i, ‖f i‖) := by
      gcongr with i
      exact norm_completedBaseChangeOperator_le K E L (f i)
    _ = (‖r‖ * ‖P‖) * ∏ i, ‖f i‖ := (mul_assoc _ _ _).symm

theorem baseChangeLiftDescent_diag
    (r : CompletedBaseChange K F L →L[K] F)
    (hr : ∀ y : F, r (completedBaseChangeEmbedding K F L y) = y) (n : ℕ)
    (P : (CompletedBaseChange K E L →L[L] CompletedBaseChange K E L) [×n]→L[L]
      ((CompletedBaseChange K E L [⋀^Fin n]→L[L] CompletedBaseChange K F L) →L[L]
        (CompletedBaseChange K E L [⋀^Fin n]→L[L] CompletedBaseChange K F L)))
    (hP : ∀ f, P (fun _ => f) = Round24Transfer.Q L (Fin n)
      (CompletedBaseChange K E L) (CompletedBaseChange K E L) (CompletedBaseChange K F L) f)
    (f : E →L[K] E) :
    baseChangeLiftDescent K E F L r n P (fun _ => f) = Round24Transfer.Q K (Fin n) E E F f := by
  ext m x
  simp only [baseChangeLiftDescent_apply, hP, Round24Transfer.Q,
    ContinuousAlternatingMap.compContinuousLinearMapCLM_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply]
  change r ((baseChangeAlternatingForms K E F L n m)
    (fun i => completedBaseChangeOperator K E L f (completedBaseChangeEmbedding K E L (x i)))) =
      m (fun i => f (x i))
  simp_rw [completedBaseChangeOperator_embedding]
  rw [baseChangeAlternatingForms_embedding, hr]

variable [CompleteSpace F]

/-- A lift over the completed base change descends to a lift over `K` of no larger norm
(Proposition D.9). -/
theorem exists_baseChangeLiftDescent (n : ℕ)
    (P : (CompletedBaseChange K E L →L[L] CompletedBaseChange K E L) [×n]→L[L]
      ((CompletedBaseChange K E L [⋀^Fin n]→L[L] CompletedBaseChange K F L) →L[L]
        (CompletedBaseChange K E L [⋀^Fin n]→L[L] CompletedBaseChange K F L)))
    (hP : ∀ f, P (fun _ => f) = Round24Transfer.Q L (Fin n)
      (CompletedBaseChange K E L) (CompletedBaseChange K E L) (CompletedBaseChange K F L) f) :
    ∃ P₁ : (E →L[K] E) [×n]→L[K]
        ((E [⋀^Fin n]→L[K] F) →L[K] (E [⋀^Fin n]→L[K] F)),
      ‖P₁‖ ≤ ‖P‖ ∧ ∀ f, P₁ (fun _ => f) = Round24Transfer.Q K (Fin n) E E F f := by
  obtain ⟨r, hr, hfix⟩ := exists_completedBaseChange_retraction K F L
  refine ⟨baseChangeLiftDescent K E F L r n P, ?_, baseChangeLiftDescent_diag K E F L r hfix n P hP⟩
  apply (norm_baseChangeLiftDescent_le K E F L r n P).trans
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hr (norm_nonneg P)

/-- A bounded lift over the completed base change gives one over `K`. -/
theorem hasBoundedLift_of_completedBaseChange (n : ℕ)
    (h : Round24Transfer.HasBoundedLift L (Fin n) (CompletedBaseChange K E L)
      (CompletedBaseChange K E L) (CompletedBaseChange K F L)) :
    Round24Transfer.HasBoundedLift K (Fin n) E E F := by
  unfold Round24Transfer.HasBoundedLift at h ⊢
  rw [Fintype.card_fin] at h ⊢
  obtain ⟨P, hP⟩ := h
  obtain ⟨P₁, _, hP₁⟩ := exists_baseChangeLiftDescent K E F L n P hP
  exact ⟨P₁, hP₁⟩

/-- If there is no bounded lift over `K`, there is none over the completed base change. -/
theorem not_hasBoundedLift_completedBaseChange (n : ℕ)
    (h : ¬ Round24Transfer.HasBoundedLift K (Fin n) E E F) :
    ¬ Round24Transfer.HasBoundedLift L (Fin n) (CompletedBaseChange K E L)
      (CompletedBaseChange K E L) (CompletedBaseChange K F L) :=
  fun hL => h (hasBoundedLift_of_completedBaseChange K E F L n hL)

/-- If the pullback is not analytic at some point over `K`, then over the completed base
change it is analytic nowhere (Proposition D.9). -/
theorem not_analyticAt_completedBaseChange_of_not_analyticAt (n : ℕ) {f₀ : E →L[K] E}
    (h : ¬ AnalyticAt K (Round24Transfer.Q K (Fin n) E E F) f₀)
    (g₀ : CompletedBaseChange K E L →L[L] CompletedBaseChange K E L) :
    ¬ AnalyticAt L (Round24Transfer.Q L (Fin n) (CompletedBaseChange K E L)
      (CompletedBaseChange K E L) (CompletedBaseChange K F L)) g₀ := by
  intro hg
  obtain ⟨P, hP⟩ := hasBoundedLift_of_completedBaseChange K E F L n
    (Round24Transfer.hasBoundedLift_of_analyticAt hg)
  exact h (Round24Transfer.cpolynomialAt_of_lift P hP f₀).analyticAt

end AlternatingAnalytic
