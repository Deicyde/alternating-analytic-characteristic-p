import AlternatingAnalytic.Analysis.AnalyticFamilies
import AlternatingAnalytic.Analysis.FiniteCoordinateReflection
import AlternatingAnalytic.Analysis.LiftCriterion
import Mathlib.Analysis.Analytic.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.LinearIsometry

/-!
# Finite coordinate analytic alternating morphism families

The ambient joint action is the diagonal of a bounded `(k + 1)`-linear map
(`paper/charp.tex`, `fam:eq:ambient-polynomial`). Reflection through the closed
isometric inclusion that forgets alternation then proves `fam:cor:finite-families`.
Neither the field nor the normed fibers need be complete, and there is no
restriction on the characteristic or the degree.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace AlternatingAnalytic

variable {K E E' F F' P : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup E'] [NormedSpace K E']
  [NormedAddCommGroup F] [NormedSpace K F]
  [NormedAddCommGroup F'] [NormedSpace K F']
  [NormedAddCommGroup P] [NormedSpace K P]

/-- Forget alternation in the values of an operator on alternating maps. -/
def alternatingMapActionInclusion (k : ℕ) :
    ((E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F')) →ₗᵢ[K]
      ((E [⋀^Fin k]→L[K] F) →L[K]
        ContinuousMultilinearMap K (fun _ : Fin k => E') F') :=
  (ContinuousAlternatingMap.toContinuousMultilinearMapLI
    (𝕜 := K) (ι := Fin k) (E := E') (F := F')).postcomp

@[simp]
theorem alternatingMapActionInclusion_apply (k : ℕ)
    (T : (E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F'))
    (m : E [⋀^Fin k]→L[K] F) (x : Fin k → E') :
    alternatingMapActionInclusion (K := K) (E := E) (E' := E') (F := F) (F' := F') k
      T m x = T m x := rfl

/-- The ambient inclusion has closed range without completeness assumptions. -/
theorem isClosed_range_alternatingMapActionInclusion (k : ℕ) :
    IsClosed (Set.range (alternatingMapActionInclusion
      (K := K) (E := E) (E' := E') (F := F) (F' := F') k)) :=
  (ContinuousAlternatingMap.toContinuousMultilinearMapLI
    (𝕜 := K) (ι := Fin k) (E := E') (F := F')).isClosed_range_postcomp
      ContinuousAlternatingMap.isClosed_range_toContinuousMultilinearMap

/-- The bounded `(k + 1)`-linear representative of `fam:eq:ambient-polynomial`. -/
def ambientAlternatingMapAction (k : ℕ) :
    ContinuousMultilinearMap K (fun _ : Fin (k + 1) => (E' →L[K] E) × (F →L[K] F'))
      ((E [⋀^Fin k]→L[K] F) →L[K] ContinuousMultilinearMap K (fun _ : Fin k => E') F') := by
  let post : ((E' →L[K] E) × (F →L[K] F')) →L[K]
      ContinuousMultilinearMap K (fun _ : Fin k => E') F →L[K]
      ContinuousMultilinearMap K (fun _ : Fin k => E') F' :=
    (ContinuousLinearMap.compContinuousMultilinearMapL K (fun _ : Fin k => E') F F').comp
      (ContinuousLinearMap.snd K _ _)
  let postOp := (ContinuousLinearMap.compL K (E [⋀^Fin k]→L[K] F)
    (ContinuousMultilinearMap K (fun _ : Fin k => E') F)
    (ContinuousMultilinearMap K (fun _ : Fin k => E') F')).comp post
  let curried : ContinuousMultilinearMap K
      (fun _ : Fin k => (E' →L[K] E) × (F →L[K] F'))
      (((E' →L[K] E) × (F →L[K] F')) →L[K]
        ((E [⋀^Fin k]→L[K] F) →L[K] ContinuousMultilinearMap K (fun _ : Fin k => E') F')) :=
    postOp.flip.compContinuousMultilinearMap
      ((Round24Transfer.ambLift K (Fin k) E' E F).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.fst K (E' →L[K] E) (F →L[K] F')))
  exact ContinuousMultilinearMap.uncurryRight
    (𝕜 := K) (G := (E [⋀^Fin k]→L[K] F) →L[K]
      ContinuousMultilinearMap K (fun _ : Fin k => E') F')
    (Ei := fun _ : Fin (k + 1) => (E' →L[K] E) × (F →L[K] F')) curried

@[simp]
theorem ambientAlternatingMapAction_apply (k : ℕ)
    (h : Fin (k + 1) → (E' →L[K] E) × (F →L[K] F'))
    (m : E [⋀^Fin k]→L[K] F) (x : Fin k → E') :
    ambientAlternatingMapAction (K := K) (E := E) (E' := E') (F := F) (F' := F') k h m x =
      (h (Fin.last k)).2 (m fun i => (h i.castSucc).1 (x i)) := rfl

/-- The pointwise estimate for the ambient multilinear representative. -/
theorem ambientAlternatingMapAction_bound (k : ℕ)
    (h : Fin (k + 1) → (E' →L[K] E) × (F →L[K] F'))
    (m : E [⋀^Fin k]→L[K] F) (x : Fin k → E') :
    ‖ambientAlternatingMapAction (K := K) (E := E) (E' := E') (F := F) (F' := F') k h m x‖ ≤
      (∏ i, ‖h i‖) * ‖m‖ * ∏ i, ‖x i‖ := by
  rw [ambientAlternatingMapAction_apply]
  calc
    ‖(h (Fin.last k)).2 (m fun i => (h i.castSucc).1 (x i))‖ ≤
        ‖h (Fin.last k)‖ * (‖m‖ * ∏ i, (‖h i.castSucc‖ * ‖x i‖)) := by
      apply le_trans ((h (Fin.last k)).2.le_opNorm _)
      gcongr
      · exact norm_snd_le _
      · apply m.le_opNorm_mul_prod_of_le
        intro i
        exact ((h i.castSucc).1.le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (norm_fst_le _) (norm_nonneg _))
    _ = (∏ i, ‖h i‖) * ‖m‖ * ∏ i, ‖x i‖ := by
      rw [Finset.prod_mul_distrib, Fin.prod_univ_castSucc]
      ring

-- Fix the standard operator norm for the nested operator codomain.
local instance ambientAlternatingMapActionNorm (k : ℕ) :
    Norm (ContinuousMultilinearMap K
      (fun _ : Fin (k + 1) => (E' →L[K] E) × (F →L[K] F'))
      ((E [⋀^Fin k]→L[K] F) →L[K]
        ContinuousMultilinearMap K (fun _ : Fin k => E') F')) :=
  ContinuousMultilinearMap.hasOpNorm
    (𝕜 := K) (E := fun _ : Fin (k + 1) => (E' →L[K] E) × (F →L[K] F'))
    (G := (E [⋀^Fin k]→L[K] F) →L[K]
      ContinuousMultilinearMap K (fun _ : Fin k => E') F')

/-- The ambient representative has operator norm at most one. -/
theorem norm_ambientAlternatingMapAction_le (k : ℕ) :
    ‖ambientAlternatingMapAction (K := K) (E := E) (E' := E') (F := F) (F' := F') k‖ ≤ 1 := by
  apply ContinuousMultilinearMap.opNorm_le_bound zero_le_one
  intro h
  rw [one_mul]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro m
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro x
  exact ambientAlternatingMapAction_bound k h m x

/-- The diagonal of the bounded multilinear representative is continuously
polynomial at every point of the joint hom space. -/
theorem cpolynomialAt_ambientAlternatingMapAction_diagonal (k : ℕ)
    (h : (E' →L[K] E) × (F →L[K] F')) :
    CPolynomialAt K
      (fun h : (E' →L[K] E) × (F →L[K] F') =>
        ambientAlternatingMapAction (K := K) (E := E) (E' := E') (F := F) (F' := F') k
          (fun _ => h)) h := by
  let diagonal : ((E' →L[K] E) × (F →L[K] F')) →L[K]
      (Fin (k + 1) → (E' →L[K] E) × (F →L[K] F')) :=
    ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id K _
  exact (ContinuousMultilinearMap.cpolynomialAt
    (𝕜 := K)
    (F := (E [⋀^Fin k]→L[K] F) →L[K]
      ContinuousMultilinearMap K (fun _ : Fin k => E') F')
    (f := ambientAlternatingMapAction
      (K := K) (E := E) (E' := E') (F := F) (F' := F') k)).comp
      (diagonal.cpolynomialAt h)

/-- The diagonal of the bounded multilinear representative is analytic. -/
theorem analyticAt_ambientAlternatingMapAction_diagonal (k : ℕ)
    (h : (E' →L[K] E) × (F →L[K] F')) :
    AnalyticAt K
      (fun h : (E' →L[K] E) × (F →L[K] F') =>
        ambientAlternatingMapAction (K := K) (E := E) (E' := E') (F := F) (F' := F') k
          (fun _ => h)) h := by
  exact (cpolynomialAt_ambientAlternatingMapAction_diagonal k h).analyticAt

/-- The diagonal of the ambient representative is the existing joint action
followed by the inclusion that forgets alternation. -/
theorem ambientAlternatingMapAction_diag (k : ℕ)
    (h : (E' →L[K] E) × (F →L[K] F')) :
    ambientAlternatingMapAction (K := K) (E := E) (E' := E') (F := F) (F' := F') k
      (fun _ => h) =
    alternatingMapActionInclusion (K := K) (E := E) (E' := E') (F := F) (F' := F') k
      (alternatingMapAction k h) := by
  ext m x
  rfl

/-- The joint action is continuously polynomial at every point after forgetting
alternation, with no completeness or characteristic assumption. -/
theorem cpolynomialAt_ambient_alternatingMapAction (k : ℕ)
    (h : (E' →L[K] E) × (F →L[K] F')) :
    CPolynomialAt K
      (alternatingMapActionInclusion (K := K) (E := E) (E' := E') (F := F) (F' := F') k ∘
        alternatingMapAction k) h := by
  simpa only [Function.comp_def, ambientAlternatingMapAction_diag] using
    cpolynomialAt_ambientAlternatingMapAction_diagonal k h

/-- The joint action is analytic after forgetting alternation. -/
theorem analyticAt_ambient_alternatingMapAction (k : ℕ)
    (h : (E' →L[K] E) × (F →L[K] F')) :
    AnalyticAt K (fun h : (E' →L[K] E) × (F →L[K] F') =>
      alternatingMapActionInclusion (K := K) (E := E) (E' := E') (F := F) (F' := F') k
        (alternatingMapAction k h)) h := by
  exact (cpolynomialAt_ambient_alternatingMapAction k h).analyticAt

/-- All conclusions of `fam:eq:ambient-polynomial`: the closed linear isometric
inclusion, the bounded `(k + 1)`-linear representative and its exact diagonal,
and continuous polynomiality at every point of the joint hom space. -/
theorem ambient_alternating_map_action_full (k : ℕ) :
    let j := alternatingMapActionInclusion
      (K := K) (E := E) (E' := E') (F := F) (F' := F') k
    let B := ambientAlternatingMapAction
      (K := K) (E := E) (E' := E') (F := F) (F' := F') k
    Isometry j ∧ IsClosed (Set.range j) ∧
      (∀ (T : (E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F'))
        (m : E [⋀^Fin k]→L[K] F) (x : Fin k → E'), j T m x = T m x) ∧
      (∀ (z : Fin (k + 1) → (E' →L[K] E) × (F →L[K] F'))
        (m : E [⋀^Fin k]→L[K] F) (x : Fin k → E'),
        B z m x = (z (Fin.last k)).2 (m fun i => (z i.castSucc).1 (x i))) ∧
      ‖B‖ ≤ 1 ∧
      (∀ h : (E' →L[K] E) × (F →L[K] F'),
        B (fun _ => h) = j (alternatingMapAction k h)) ∧
      (∀ h : (E' →L[K] E) × (F →L[K] F'),
        CPolynomialAt K (j ∘ alternatingMapAction k) h) := by
  exact ⟨(alternatingMapActionInclusion k).isometry,
    isClosed_range_alternatingMapActionInclusion k,
    alternatingMapActionInclusion_apply k, ambientAlternatingMapAction_apply k,
    norm_ambientAlternatingMapAction_le k, ambientAlternatingMapAction_diag k,
    cpolynomialAt_ambient_alternatingMapAction k⟩

/-- Continuous finite coordinates suffice for the action of an analytic family
to be analytic, even when the field and fibers are incomplete. -/
theorem analyticAt_alternatingMapAction_comp_of_finite_coordinates {d : ℕ}
    (e : P ≃L[K] (Fin d → K)) (k : ℕ)
    {γ : P → (E' →L[K] E) × (F →L[K] F')} {x : P}
    (hγ : AnalyticAt K γ x) : AnalyticAt K (alternatingMapAction k ∘ γ) x := by
  apply analyticAt_of_closed_linearIsometry_of_equiv e
    (G := (E [⋀^Fin k]→L[K] F) →L[K]
      ContinuousMultilinearMap K (fun _ : Fin k => E') F')
    (alternatingMapActionInclusion (K := K) (E := E) (E' := E') (F := F) (F' := F') k)
    (isClosed_range_alternatingMapActionInclusion
      (K := K) (E := E) (E' := E') (F := F) (F' := F') k)
  exact (analyticAt_ambient_alternatingMapAction k (γ x)).comp hγ

/-- Analytic families with continuous finite coordinates are admissible. -/
theorem isAdmissibleOn_of_finite_coordinates {d : ℕ}
    (e : P ≃L[K] (Fin d → K)) (k : ℕ)
    {γ : P → (E' →L[K] E) × (F →L[K] F')} {U : Set P}
    (hγ : AnalyticOnNhd K γ U) : IsAdmissibleOn k γ U :=
  ⟨hγ, fun x hx => analyticAt_alternatingMapAction_comp_of_finite_coordinates e k (hγ x hx)⟩

/-- `fam:cor:finite-families`: every analytic morphism family on an open subset
of `K^d` is admissible, in every characteristic and degree, with arbitrary
normed fibers. -/
theorem finite_coordinate_analytic_families (k : ℕ) {d : ℕ}
    {U : Set (Fin d → K)} (hU : IsOpen U)
    {γ : (Fin d → K) → (E' →L[K] E) × (F →L[K] F')}
    (hγ : AnalyticOn K γ U) : IsAdmissibleOn k γ U :=
  isAdmissibleOn_of_finite_coordinates (ContinuousLinearEquiv.refl K (Fin d → K)) k
    (hU.analyticOn_iff_analyticOnNhd.mp hγ)

end AlternatingAnalytic
