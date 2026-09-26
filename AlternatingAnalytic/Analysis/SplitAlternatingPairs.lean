import AlternatingAnalytic.Analysis.SortedBasisLift
import AlternatingAnalytic.Analysis.UniversalAlternatingTargets
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

/-!
# Split alternating pairs

A split pair has a bounded linear retraction from continuous multilinear maps onto
continuous alternating maps. A split destination gives a polynomial incoming joint
action, with an explicit lift indexed by `Option (Fin k)`, including degree zero.
All spaces carry their ordinary norms; no norm bound on the retraction is imposed.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace AlternatingAnalytic

variable (K : Type*) [NontriviallyNormedField K]

/-- The actual alternating inclusion has a bounded linear retraction. -/
def IsSplitAlternatingPair (k : ℕ) (E F : Type*)
    [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup F] [NormedSpace K F] : Prop :=
  ∃ r : (E [×k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F),
    ∀ m : E [⋀^Fin k]→L[K] F, r m.toContinuousMultilinearMap = m

variable {K} {E E' F F' : Type*}
  [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup E'] [NormedSpace K E']
  [NormedAddCommGroup F] [NormedSpace K F]
  [NormedAddCommGroup F'] [NormedSpace K F']

/-- The destination retraction lift, depending linearly on the pushforward operator. -/
def splitDestinationPushforwardLift (k : ℕ)
    (r : (E' [×k]→L[K] F') →L[K] (E' [⋀^Fin k]→L[K] F')) :
    (F →L[K] F') →L[K] ContinuousMultilinearMap K (fun _ : Fin k => E' →L[K] E)
      ((E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F')) :=
  let compose :
      ((E [⋀^Fin k]→L[K] F') →L[K] (E' [⋀^Fin k]→L[K] F')) →L[K]
        (F →L[K] F') →L[K]
          ((E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F')) :=
    ((ContinuousLinearMap.compL K (E [⋀^Fin k]→L[K] F)
      (E [⋀^Fin k]→L[K] F') (E' [⋀^Fin k]→L[K] F')).flip.comp
      (ContinuousLinearMap.compContinuousAlternatingMapCLM K E F F' (Fin k))).flip
  (compose.compContinuousMultilinearMap
    (contractingRetractionLift (E' := E) k r)).flipLinear
      (𝕜 := K) (E := fun _ : Fin k => E' →L[K] E)
      (G := F →L[K] F')
      (G' := (E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F'))

/-- The bounded `(k + 1)`-linear incoming lift with one pushforward slot. -/
def splitDestinationLift (k : ℕ)
    (r : (E' [×k]→L[K] F') →L[K] (E' [⋀^Fin k]→L[K] F')) :
    ContinuousMultilinearMap K
      (fun _ : Option (Fin k) => (E' →L[K] E) × (F →L[K] F'))
      ((E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F')) :=
  ((splitDestinationPushforwardLift (E := E) (F := F) k r).continuousMultilinearMapOption
    (F := (E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F')))
    |>.compContinuousLinearMap (fun _ =>
      (ContinuousLinearMap.snd K (E' →L[K] E) (F →L[K] F')).prod
        (ContinuousLinearMap.pi fun _ : Fin k =>
          ContinuousLinearMap.fst K (E' →L[K] E) (F →L[K] F')))

@[simp]
theorem splitDestinationLift_apply (k : ℕ)
    (r : (E' [×k]→L[K] F') →L[K] (E' [⋀^Fin k]→L[K] F'))
    (z : Option (Fin k) → (E' →L[K] E) × (F →L[K] F'))
    (m : E [⋀^Fin k]→L[K] F) :
    splitDestinationLift k r z m =
      r (((z none).2.compContinuousMultilinearMap m.toContinuousMultilinearMap).compContinuousLinearMap
        fun i => (z (some i)).1) := rfl

/-- The retraction property identifies the diagonal with the actual incoming action. -/
theorem splitDestinationLift_diag (k : ℕ)
    (r : (E' [×k]→L[K] F') →L[K] (E' [⋀^Fin k]→L[K] F'))
    (hr : ∀ m : E' [⋀^Fin k]→L[K] F', r m.toContinuousMultilinearMap = m)
    (a : (E' →L[K] E) × (F →L[K] F')) :
    splitDestinationLift k r (fun _ => a) = alternatingMapAction k a := by
  change (contractingRetractionLift k r (fun _ => a.1)).comp
    (ContinuousLinearMap.compContinuousAlternatingMapCLM K E F F' (Fin k) a.2) = _
  rw [contractingRetractionLift_diag k r hr]
  exact (alternatingMapAction_eq_target_precomposition k a).symm

/-- A split destination gives polynomial target-valued precomposition. -/
theorem cpolynomialAt_precomposition_of_split_destination
    (k : ℕ) (h : IsSplitAlternatingPair K k E' F') (u : E' →L[K] E) :
    CPolynomialAt K
      (ContinuousAlternatingMap.compContinuousLinearMapCLM :
        (E' →L[K] E) →
          (E [⋀^Fin k]→L[K] F') →L[K] (E' [⋀^Fin k]→L[K] F')) u := by
  obtain ⟨r, hr⟩ := h
  exact Round24Transfer.cpolynomialAt_of_lift
    (contractingRetractionLift (E' := E) k r)
    (contractingRetractionLift_diag k r hr) u

/-- The actual alternating action into a split pair is jointly polynomial. -/
theorem cpolynomialAt_alternatingMapAction_of_split_destination
    (k : ℕ) (h : IsSplitAlternatingPair K k E' F')
    (a₀ : (E' →L[K] E) × (F →L[K] F')) :
    CPolynomialAt K (alternatingMapAction (K := K) (E := E) (E' := E')
      (F := F) (F' := F') k) a₀ := by
  exact cpolynomialAt_alternatingMapAction_of_target_precomposition k a₀
    (cpolynomialAt_precomposition_of_split_destination k h a₀.1)

/-- The actual alternating action into a split pair is jointly analytic. -/
theorem analyticAt_alternatingMapAction_of_split_destination
    (k : ℕ) (h : IsSplitAlternatingPair K k E' F')
    (a₀ : (E' →L[K] E) × (F →L[K] F')) :
    AnalyticAt K (alternatingMapAction (K := K) (E := E) (E' := E')
      (F := F) (F' := F') k) a₀ :=
  (cpolynomialAt_alternatingMapAction_of_split_destination k h a₀).analyticAt

/-- The incoming alternating action into a split pair is analytic everywhere. -/
theorem analyticOnNhd_alternatingMapAction_of_split_destination
    (k : ℕ) (h : IsSplitAlternatingPair K k E' F') :
    AnalyticOnNhd K (alternatingMapAction (K := K) (E := E) (E' := E')
      (F := F) (F' := F') k) Set.univ := by
  intro a₀ _
  exact analyticAt_alternatingMapAction_of_split_destination k h a₀

/-- A split destination admits the concrete incoming lift with its prescribed formula,
exact diagonal, polynomial regularity at every operator pair, and global analyticity. -/
theorem split_destination_polynomial_action
    (k : ℕ) (h : IsSplitAlternatingPair K k E' F') :
    ∃ r : (E' [×k]→L[K] F') →L[K] (E' [⋀^Fin k]→L[K] F'),
      (∀ m : E' [⋀^Fin k]→L[K] F', r m.toContinuousMultilinearMap = m) ∧
      ∃ L : ContinuousMultilinearMap K
          (fun _ : Option (Fin k) => (E' →L[K] E) × (F →L[K] F'))
          ((E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F')),
        L = splitDestinationLift k r ∧
        (∀ (z : Option (Fin k) → (E' →L[K] E) × (F →L[K] F'))
          (m : E [⋀^Fin k]→L[K] F),
          L z m = r (((z none).2.compContinuousMultilinearMap
            m.toContinuousMultilinearMap).compContinuousLinearMap fun i => (z (some i)).1)) ∧
        (∀ a : (E' →L[K] E) × (F →L[K] F'),
          L (fun _ => a) = alternatingMapAction k a) ∧
        (∀ a₀ : (E' →L[K] E) × (F →L[K] F'),
          CPolynomialAt K (alternatingMapAction (K := K) (E := E) (E' := E')
            (F := F) (F' := F') k) a₀) ∧
        AnalyticOnNhd K (alternatingMapAction (K := K) (E := E) (E' := E')
          (F := F) (F' := F') k) Set.univ := by
  obtain ⟨r, hr⟩ := h
  exact ⟨r, hr, splitDestinationLift k r, rfl,
    splitDestinationLift_apply k r, splitDestinationLift_diag k r hr,
    cpolynomialAt_alternatingMapAction_of_split_destination k ⟨r, hr⟩,
    analyticOnNhd_alternatingMapAction_of_split_destination k ⟨r, hr⟩⟩

end AlternatingAnalytic
