import AlternatingAnalytic.Analysis.BoundedRetractionLift
import AlternatingAnalytic.Analysis.FiniteCoordinateDeterminant
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Finite coordinate bases in the domain

If `E` has a finite basis with continuous coordinate functionals, the determinant
formula over increasing basis tuples gives a bounded retraction from multilinear to
alternating maps on `E`, and hence a bounded lift of `A^k`. This is the source case
of Proposition 4.1(2). The norm bound `k! ∑_s ∏_a ‖ε_{s_a}‖ ‖e_{s_a}‖` uses the real
factorial, and all degrees, including zero, are allowed. In Lean, `A^k` is
`LiftCriterion.Q`, the map `f ↦ (m ↦ m ∘ (f, …, f))`.
-/

noncomputable section

namespace AlternatingAnalytic

open scoped BigOperators
open Module

variable {K E E' F : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup E'] [NormedSpace K E']
  [NormedAddCommGroup F] [NormedSpace K F]
  {d : ℕ}

/-- The `i`-th coordinate functional, as a continuous linear map. -/
def finiteCoordinateFunctional (b : Basis (Fin d) K E)
    (hb : ∀ i, Continuous (b.coord i)) (i : Fin d) : E →L[K] K :=
  ⟨b.coord i, hb i⟩

@[simp] theorem finiteCoordinateFunctional_apply (b : Basis (Fin d) K E)
    (hb : ∀ i, Continuous (b.coord i)) (i : Fin d) (x : E) :
    finiteCoordinateFunctional b hb i x = b.coord i x := rfl

/-- The norm bound `k! ∑_s ∏_a ‖ε_{s_a}‖ ‖e_{s_a}‖` of Proposition 4.1. -/
def finiteCoordinateBound (b : Basis (Fin d) K E)
    (hb : ∀ i, Continuous (b.coord i)) (k : ℕ) : ℝ :=
  (k.factorial : ℝ) * ∑ s : Set.powersetCard (Fin d) k,
    ∏ a : Fin k,
      (‖finiteCoordinateFunctional b hb (Set.powersetCard.ofFinEmbEquiv.symm s a)‖ *
        ‖b (Set.powersetCard.ofFinEmbEquiv.symm s a)‖)

theorem finiteCoordinateBound_nonneg (b : Basis (Fin d) K E)
    (hb : ∀ i, Continuous (b.coord i)) (k : ℕ) :
    0 ≤ finiteCoordinateBound b hb k := by
  unfold finiteCoordinateBound
  positivity

/-- Extend the values on increasing basis tuples through the exterior basis. -/
def finiteCoordinateAlternatingMap (b : Basis (Fin d) K E) (k : ℕ) :
    (E [×k]→L[K] F) →ₗ[K] (E [⋀^Fin k]→ₗ[K] F) :=
  exteriorPower.alternatingMapLinearEquiv.symm.toLinearMap.comp
    (((b.exteriorPower k).constr K).toLinearMap.comp
      ({ toFun := fun g s => g (b ∘ Set.powersetCard.ofFinEmbEquiv.symm s)
         map_add' := by intros; rfl
         map_smul' := by intros; rfl } :
          (E [×k]→L[K] F) →ₗ[K] (Set.powersetCard (Fin d) k → F)))

theorem finiteCoordinateAlternatingMap_apply (b : Basis (Fin d) K E)
    (hb : ∀ i, Continuous (b.coord i)) (k : ℕ)
    (g : E [×k]→L[K] F) (x : Fin k → E) :
    finiteCoordinateAlternatingMap b k g x =
      ∑ s : Set.powersetCard (Fin d) k,
        (Matrix.of fun a j =>
          finiteCoordinateFunctional b hb
            (Set.powersetCard.ofFinEmbEquiv.symm s a) (x j)).det •
          g (fun a => b (Set.powersetCard.ofFinEmbEquiv.symm s a)) := by
  classical
  change (b.exteriorPower k).constr K
    (fun s => g (b ∘ Set.powersetCard.ofFinEmbEquiv.symm s))
    (exteriorPower.ιMulti K k x) = _
  rw [Basis.constr_apply, Finsupp.sum_fintype _ _ (by intros; simp)]
  apply Finset.sum_congr rfl
  intro s _
  rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
  congr 1
  exact Matrix.det_transpose _

theorem finiteCoordinateAlternatingMap_retract (b : Basis (Fin d) K E) (k : ℕ)
    (m : E [⋀^Fin k]→L[K] F) :
    finiteCoordinateAlternatingMap b k m.toContinuousMultilinearMap = m.toAlternatingMap := by
  apply exteriorPower.alternatingMapLinearEquiv.injective
  change exteriorPower.alternatingMapLinearEquiv
    (exteriorPower.alternatingMapLinearEquiv.symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  apply (b.exteriorPower k).ext
  intro s
  change (b.exteriorPower k).constr K
    (fun t => m (b ∘ Set.powersetCard.ofFinEmbEquiv.symm t))
    ((b.exteriorPower k) s) = _
  rw [Basis.constr_basis, exteriorPower.basis_apply]
  simp [exteriorPower.ιMulti_family]

theorem norm_finiteCoordinateAlternatingMap_le (b : Basis (Fin d) K E)
    (hb : ∀ i, Continuous (b.coord i)) (k : ℕ)
    (g : E [×k]→L[K] F) (x : Fin k → E) :
    ‖finiteCoordinateAlternatingMap b k g x‖ ≤
      finiteCoordinateBound b hb k * ‖g‖ * ∏ j, ‖x j‖ := by
  classical
  rw [finiteCoordinateAlternatingMap_apply b hb]
  calc
    _ ≤ ∑ s : Set.powersetCard (Fin d) k,
        ‖(Matrix.of fun a j => finiteCoordinateFunctional b hb
          (Set.powersetCard.ofFinEmbEquiv.symm s a) (x j)).det •
          g (fun a => b (Set.powersetCard.ofFinEmbEquiv.symm s a))‖ := norm_sum_le _ _
    _ ≤ ∑ s : Set.powersetCard (Fin d) k,
        (k.factorial : ℝ) *
          (∏ a : Fin k, (‖finiteCoordinateFunctional b hb
            (Set.powersetCard.ofFinEmbEquiv.symm s a)‖ *
            ‖b (Set.powersetCard.ofFinEmbEquiv.symm s a)‖)) * ‖g‖ * ∏ j, ‖x j‖ := by
      apply Finset.sum_le_sum
      intro s _
      let t := Set.powersetCard.ofFinEmbEquiv.symm s
      have hdet := norm_det_le_factorial_mul_prod
        (Matrix.of fun a j => finiteCoordinateFunctional b hb (t a) (x j))
        (fun a => ‖finiteCoordinateFunctional b hb (t a)‖) (fun j => ‖x j‖)
        (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
        (fun a j => (finiteCoordinateFunctional b hb (t a)).le_opNorm (x j))
      rw [norm_smul]
      calc
        _ ≤ ((k.factorial : ℝ) * (∏ a, ‖finiteCoordinateFunctional b hb (t a)‖) *
            ∏ j, ‖x j‖) * (‖g‖ * ∏ a, ‖b (t a)‖) :=
          mul_le_mul hdet (g.le_opNorm _) (norm_nonneg _) (by positivity)
        _ = _ := by rw [Finset.prod_mul_distrib]; ring
    _ = _ := by
      simp only [finiteCoordinateBound, Finset.sum_mul, Finset.mul_sum]

/-- A bounded retraction from multilinear to alternating maps, in every degree. -/
def finiteCoordinateRetraction (b : Basis (Fin d) K E)
    (hb : ∀ i, Continuous (b.coord i)) (k : ℕ) :
    (E [×k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F) :=
  AlternatingMap.mkContinuousLinear (finiteCoordinateAlternatingMap b k)
    (finiteCoordinateBound b hb k) (norm_finiteCoordinateAlternatingMap_le b hb k)

theorem finiteCoordinateRetraction_apply (b : Basis (Fin d) K E)
    (hb : ∀ i, Continuous (b.coord i)) (k : ℕ)
    (g : E [×k]→L[K] F) (x : Fin k → E) :
    finiteCoordinateRetraction b hb k g x =
      ∑ s : Set.powersetCard (Fin d) k,
        (Matrix.of fun a j => finiteCoordinateFunctional b hb
          (Set.powersetCard.ofFinEmbEquiv.symm s a) (x j)).det •
          g (fun a => b (Set.powersetCard.ofFinEmbEquiv.symm s a)) :=
  finiteCoordinateAlternatingMap_apply b hb k g x

theorem norm_finiteCoordinateRetraction_apply_le (b : Basis (Fin d) K E)
    (hb : ∀ i, Continuous (b.coord i)) (k : ℕ)
    (g : E [×k]→L[K] F) (x : Fin k → E) :
    ‖finiteCoordinateRetraction b hb k g x‖ ≤
      finiteCoordinateBound b hb k * ‖g‖ * ∏ j, ‖x j‖ :=
  norm_finiteCoordinateAlternatingMap_le b hb k g x

theorem norm_finiteCoordinateRetraction_le (b : Basis (Fin d) K E)
    (hb : ∀ i, Continuous (b.coord i)) (k : ℕ) :
    ‖finiteCoordinateRetraction (F := F) b hb k‖ ≤ finiteCoordinateBound b hb k :=
  AlternatingMap.mkContinuousLinear_norm_le _ (finiteCoordinateBound_nonneg b hb k) _

theorem finiteCoordinateRetraction_retract (b : Basis (Fin d) K E)
    (hb : ∀ i, Continuous (b.coord i)) (k : ℕ) (m : E [⋀^Fin k]→L[K] F) :
    finiteCoordinateRetraction b hb k m.toContinuousMultilinearMap = m := by
  ext x
  exact DFunLike.congr_fun (finiteCoordinateAlternatingMap_retract b k m) x

noncomputable local instance finiteCoordinateDomainLiftNorm (k : ℕ) :
    Norm ((E →L[K] E') [×k]→L[K]
      ((E' [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F))) :=
  ContinuousMultilinearMap.hasOpNorm
    (𝕜 := K) (E := fun _ : Fin k => E →L[K] E')
    (G := (E' [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F))

/-- The bounded lift of `A^k` obtained from the coordinate retraction. -/
def finiteCoordinateDomainLift (b : Basis (Fin d) K E)
    (hb : ∀ i, Continuous (b.coord i)) (k : ℕ) :
    (E →L[K] E') [×k]→L[K]
      ((E' [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F)) :=
  contractingRetractionLift k (finiteCoordinateRetraction b hb k)

theorem finiteCoordinateDomainLift_apply (b : Basis (Fin d) K E)
    (hb : ∀ i, Continuous (b.coord i)) (k : ℕ)
    (f : Fin k → E →L[K] E') (m : E' [⋀^Fin k]→L[K] F) (x : Fin k → E) :
    finiteCoordinateDomainLift b hb k f m x =
      ∑ s : Set.powersetCard (Fin d) k,
        (Matrix.of fun a j => finiteCoordinateFunctional b hb
          (Set.powersetCard.ofFinEmbEquiv.symm s a) (x j)).det •
          m (fun a => f a (b (Set.powersetCard.ofFinEmbEquiv.symm s a))) :=
  finiteCoordinateRetraction_apply b hb k
    (m.toContinuousMultilinearMap.compContinuousLinearMap f) x

theorem norm_finiteCoordinateDomainLift_le (b : Basis (Fin d) K E)
    (hb : ∀ i, Continuous (b.coord i)) (k : ℕ) :
    ‖finiteCoordinateDomainLift (E' := E') (F := F) b hb k‖ ≤
      finiteCoordinateBound b hb k :=
  (norm_contractingRetractionLift_le_norm k _).trans
    (norm_finiteCoordinateRetraction_le b hb k)

theorem norm_finiteCoordinateDomainLift_apply_le (b : Basis (Fin d) K E)
    (hb : ∀ i, Continuous (b.coord i)) (k : ℕ)
    (f : Fin k → E →L[K] E') (m : E' [⋀^Fin k]→L[K] F) (x : Fin k → E) :
    ‖finiteCoordinateDomainLift b hb k f m x‖ ≤
      finiteCoordinateBound b hb k * ‖m‖ * (∏ a, ‖f a‖) * ∏ j, ‖x j‖ := by
  apply (norm_contractingRetractionLift_apply_le k
    (finiteCoordinateRetraction b hb k) f m x).trans
  gcongr
  exact norm_finiteCoordinateRetraction_le b hb k

theorem finiteCoordinateDomainLift_diag (b : Basis (Fin d) K E)
    (hb : ∀ i, Continuous (b.coord i)) (k : ℕ) (f : E →L[K] E') :
    finiteCoordinateDomainLift (F := F) b hb k (fun _ => f) =
      LiftCriterion.Q K (Fin k) E E' F f :=
  contractingRetractionLift_diag k _ (finiteCoordinateRetraction_retract b hb k) f

theorem hasBoundedLift_of_finiteCoordinateDomain (b : Basis (Fin d) K E)
    (hb : ∀ i, Continuous (b.coord i)) (k : ℕ) :
    LiftCriterion.HasBoundedLift K (Fin k) E E' F := by
  rw [LiftCriterion.HasBoundedLift, Fintype.card_fin]
  exact ⟨finiteCoordinateDomainLift b hb k, finiteCoordinateDomainLift_diag b hb k⟩

theorem cpolynomialAt_Q_of_finiteCoordinateDomain (b : Basis (Fin d) K E)
    (hb : ∀ i, Continuous (b.coord i)) (k : ℕ) (f₀ : E →L[K] E') :
    CPolynomialAt K (LiftCriterion.Q K (Fin k) E E' F) f₀ :=
  LiftCriterion.cpolynomialAt_of_lift (finiteCoordinateDomainLift b hb k)
    (finiteCoordinateDomainLift_diag b hb k) f₀

theorem analyticAt_Q_of_finiteCoordinateDomain (b : Basis (Fin d) K E)
    (hb : ∀ i, Continuous (b.coord i)) (k : ℕ) (f₀ : E →L[K] E') :
    AnalyticAt K (LiftCriterion.Q K (Fin k) E E' F) f₀ :=
  (cpolynomialAt_Q_of_finiteCoordinateDomain b hb k f₀).analyticAt

private theorem finiteCoordinateIndices_isEmpty {d k : ℕ} (h : d < k) :
    IsEmpty (Set.powersetCard (Fin d) k) := by
  refine ⟨fun s => ?_⟩
  have hs : k ≤ d := by
    have hc := Finset.card_le_univ s.val
    simpa only [Set.powersetCard.card_eq, Fintype.card_fin] using hc
  omega

theorem finiteCoordinateBound_eq_zero_of_lt (b : Basis (Fin d) K E)
    (hb : ∀ i, Continuous (b.coord i)) {k : ℕ} (h : d < k) :
    finiteCoordinateBound b hb k = 0 := by
  let := finiteCoordinateIndices_isEmpty h
  simp [finiteCoordinateBound]

/-- Above the coordinate dimension the defining sum is empty, so the retraction is zero. -/
theorem finiteCoordinateRetraction_eq_zero_of_lt (b : Basis (Fin d) K E)
    (hb : ∀ i, Continuous (b.coord i)) {k : ℕ} (h : d < k) :
    finiteCoordinateRetraction (F := F) b hb k = 0 := by
  let := finiteCoordinateIndices_isEmpty h
  ext g x
  simp [finiteCoordinateRetraction_apply]

theorem finiteCoordinateDomainLift_eq_zero_of_lt (b : Basis (Fin d) K E)
    (hb : ∀ i, Continuous (b.coord i)) {k : ℕ} (h : d < k) :
    finiteCoordinateDomainLift (E' := E') (F := F) b hb k = 0 := by
  let := finiteCoordinateIndices_isEmpty h
  ext f m x
  simp [finiteCoordinateDomainLift_apply]

theorem Q_eq_zero_of_finiteCoordinateDomain_lt (b : Basis (Fin d) K E)
    (hb : ∀ i, Continuous (b.coord i)) {k : ℕ} (h : d < k) (f : E →L[K] E') :
    LiftCriterion.Q K (Fin k) E E' F f = 0 := by
  rw [← finiteCoordinateDomainLift_diag b hb k f,
    finiteCoordinateDomainLift_eq_zero_of_lt b hb h]
  rfl

theorem finiteCoordinateBound_zero (b : Basis (Fin d) K E)
    (hb : ∀ i, Continuous (b.coord i)) : finiteCoordinateBound b hb 0 = 1 := by
  let : Unique (Set.powersetCard (Fin d) 0) :=
    ⟨⟨∅, rfl⟩, fun s => Subtype.ext (Finset.card_eq_zero.mp s.prop)⟩
  simp [finiteCoordinateBound]

/-- In degree zero the retraction preserves the constant value. -/
theorem finiteCoordinateRetraction_zero_apply (b : Basis (Fin d) K E)
    (hb : ∀ i, Continuous (b.coord i)) (g : E [×0]→L[K] F) (x : Fin 0 → E) :
    finiteCoordinateRetraction b hb 0 g x = g x := by
  let : Unique (Set.powersetCard (Fin d) 0) :=
    ⟨⟨∅, rfl⟩, fun s => Subtype.ext (Finset.card_eq_zero.mp s.prop)⟩
  rw [finiteCoordinateRetraction_apply, Fintype.sum_unique, Matrix.det_isEmpty, one_smul]
  exact congrArg g (Subsingleton.elim _ _)

/-- The degree-zero lift is constant in its operator arguments. -/
theorem finiteCoordinateDomainLift_zero_apply (b : Basis (Fin d) K E)
    (hb : ∀ i, Continuous (b.coord i)) (f : Fin 0 → E →L[K] E')
    (m : E' [⋀^Fin 0]→L[K] F) (x : Fin 0 → E) :
    finiteCoordinateDomainLift b hb 0 f m x = m (fun i => Fin.elim0 i) := by
  change finiteCoordinateRetraction b hb 0
    (m.toContinuousMultilinearMap.compContinuousLinearMap f) x = _
  rw [finiteCoordinateRetraction_zero_apply]
  exact congrArg m (Subsingleton.elim _ _)

theorem Q_zero_constant_of_finiteCoordinateDomain (f f' : E →L[K] E') :
    LiftCriterion.Q K (Fin 0) E E' F f =
      LiftCriterion.Q K (Fin 0) E E' F f' := by
  ext m x
  exact congrArg m (Subsingleton.elim _ _)

/-- Proposition 4.1(2), source case: the coordinate retraction and lift, their
determinant formulas and norm bounds, the diagonal identity, polynomiality and
analyticity of `A^k`, and the cases `d < k` and `k = 0`. -/
theorem finiteCoordinateDomain (b : Basis (Fin d) K E)
    (hb : ∀ i, Continuous (b.coord i)) (k : ℕ) :
    let C := finiteCoordinateBound b hb k
    let r := finiteCoordinateRetraction (F := F) b hb k
    let P := finiteCoordinateDomainLift (E' := E') (F := F) b hb k
    0 ≤ C ∧
    (∀ (g : E [×k]→L[K] F) (x : Fin k → E),
      r g x = ∑ s : Set.powersetCard (Fin d) k,
        (Matrix.of fun a j => finiteCoordinateFunctional b hb
          (Set.powersetCard.ofFinEmbEquiv.symm s a) (x j)).det •
          g (fun a => b (Set.powersetCard.ofFinEmbEquiv.symm s a))) ∧
    (∀ (g : E [×k]→L[K] F) (x : Fin k → E),
      ‖r g x‖ ≤ C * ‖g‖ * ∏ j, ‖x j‖) ∧
    ‖r‖ ≤ C ∧
    (∀ m : E [⋀^Fin k]→L[K] F, r m.toContinuousMultilinearMap = m) ∧
    (∀ (f : Fin k → E →L[K] E') (m : E' [⋀^Fin k]→L[K] F) (x : Fin k → E),
      P f m x = ∑ s : Set.powersetCard (Fin d) k,
        (Matrix.of fun a j => finiteCoordinateFunctional b hb
          (Set.powersetCard.ofFinEmbEquiv.symm s a) (x j)).det •
          m (fun a => f a (b (Set.powersetCard.ofFinEmbEquiv.symm s a)))) ∧
    (∀ (f : Fin k → E →L[K] E') (m : E' [⋀^Fin k]→L[K] F) (x : Fin k → E),
      ‖P f m x‖ ≤ C * ‖m‖ * (∏ a, ‖f a‖) * ∏ j, ‖x j‖) ∧
    ‖P‖ ≤ C ∧
    (∀ f : E →L[K] E', P (fun _ => f) = LiftCriterion.Q K (Fin k) E E' F f) ∧
    LiftCriterion.HasBoundedLift K (Fin k) E E' F ∧
    (∀ f₀ : E →L[K] E', CPolynomialAt K (LiftCriterion.Q K (Fin k) E E' F) f₀) ∧
    (∀ f₀ : E →L[K] E', AnalyticAt K (LiftCriterion.Q K (Fin k) E E' F) f₀) ∧
    (d < k → C = 0 ∧ r = 0 ∧ P = 0 ∧
      ∀ f : E →L[K] E', LiftCriterion.Q K (Fin k) E E' F f = 0) ∧
    (k = 0 → C = 1 ∧
      (∀ (g : E [×k]→L[K] F) (x : Fin k → E), r g x = g x) ∧
      ∀ f f' : E →L[K] E', LiftCriterion.Q K (Fin k) E E' F f =
        LiftCriterion.Q K (Fin k) E E' F f') := by
  dsimp only
  refine ⟨finiteCoordinateBound_nonneg b hb k,
    finiteCoordinateRetraction_apply b hb k,
    norm_finiteCoordinateRetraction_apply_le b hb k,
    norm_finiteCoordinateRetraction_le b hb k,
    finiteCoordinateRetraction_retract b hb k,
    finiteCoordinateDomainLift_apply b hb k,
    norm_finiteCoordinateDomainLift_apply_le b hb k,
    norm_finiteCoordinateDomainLift_le b hb k,
    finiteCoordinateDomainLift_diag b hb k,
    hasBoundedLift_of_finiteCoordinateDomain b hb k,
    cpolynomialAt_Q_of_finiteCoordinateDomain b hb k,
    analyticAt_Q_of_finiteCoordinateDomain b hb k, ?_, ?_⟩
  · intro h
    exact ⟨finiteCoordinateBound_eq_zero_of_lt b hb h,
      finiteCoordinateRetraction_eq_zero_of_lt b hb h,
      finiteCoordinateDomainLift_eq_zero_of_lt b hb h,
      Q_eq_zero_of_finiteCoordinateDomain_lt b hb h⟩
  · rintro rfl
    exact ⟨finiteCoordinateBound_zero b hb,
      finiteCoordinateRetraction_zero_apply b hb,
      Q_zero_constant_of_finiteCoordinateDomain⟩

end AlternatingAnalytic
