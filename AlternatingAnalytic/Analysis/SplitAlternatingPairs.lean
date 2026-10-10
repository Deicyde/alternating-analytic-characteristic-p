import AlternatingAnalytic.Analysis.SortedBasisLift
import AlternatingAnalytic.Analysis.UniversalAlternatingTargets
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

/-!
# Split alternating pairs

A pair `(E, F)` is split in degree `k` if the inclusion of alternating maps into multilinear
maps `E^k → F` has a bounded linear retraction. If the destination pair is split, the joint
action `(u, g) ↦ (m ↦ g ∘ m ∘ (u, …, u))` on morphisms is a continuous polynomial, hence
analytic. This is the first part of Lemma H.3.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace AlternatingAnalytic

variable (K : Type*) [NontriviallyNormedField K]

/-- The pair `(E, F)` is split in degree `k`: the inclusion of alternating maps into
multilinear maps has a bounded linear retraction. -/
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

/-- The lift built from the retraction `r` at the destination, as a linear function of the
operator `g : F →L[K] F'`. -/
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

/-- The bounded `(k + 1)`-linear lift of the joint action; the slot `none` carries `g`. -/
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

/-- The diagonal of `splitDestinationLift` is the joint action. -/
theorem splitDestinationLift_diag (k : ℕ)
    (r : (E' [×k]→L[K] F') →L[K] (E' [⋀^Fin k]→L[K] F'))
    (hr : ∀ m : E' [⋀^Fin k]→L[K] F', r m.toContinuousMultilinearMap = m)
    (a : (E' →L[K] E) × (F →L[K] F')) :
    splitDestinationLift k r (fun _ => a) = alternatingMapAction k a := by
  change (contractingRetractionLift k r (fun _ => a.1)).comp
    (ContinuousLinearMap.compContinuousAlternatingMapCLM K E F F' (Fin k) a.2) = _
  rw [contractingRetractionLift_diag k r hr]
  exact (alternatingMapAction_eq_target_precomposition k a).symm

/-- If `(E', F')` is split, precomposition into `F'`-valued alternating maps is a
continuous polynomial. -/
theorem cpolynomialAt_precomposition_of_split_destination
    (k : ℕ) (h : IsSplitAlternatingPair K k E' F') (u : E' →L[K] E) :
    CPolynomialAt K
      (ContinuousAlternatingMap.compContinuousLinearMapCLM :
        (E' →L[K] E) →
          (E [⋀^Fin k]→L[K] F') →L[K] (E' [⋀^Fin k]→L[K] F')) u := by
  obtain ⟨r, hr⟩ := h
  exact LiftCriterion.cpolynomialAt_of_lift
    (contractingRetractionLift (E' := E) k r)
    (contractingRetractionLift_diag k r hr) u

/-- The joint action into a split pair is a continuous polynomial. -/
theorem cpolynomialAt_alternatingMapAction_of_split_destination
    (k : ℕ) (h : IsSplitAlternatingPair K k E' F')
    (a₀ : (E' →L[K] E) × (F →L[K] F')) :
    CPolynomialAt K (alternatingMapAction (K := K) (E := E) (E' := E')
      (F := F) (F' := F') k) a₀ := by
  exact cpolynomialAt_alternatingMapAction_of_target_precomposition k a₀
    (cpolynomialAt_precomposition_of_split_destination k h a₀.1)

/-- The joint action into a split pair is analytic. -/
theorem analyticAt_alternatingMapAction_of_split_destination
    (k : ℕ) (h : IsSplitAlternatingPair K k E' F')
    (a₀ : (E' →L[K] E) × (F →L[K] F')) :
    AnalyticAt K (alternatingMapAction (K := K) (E := E) (E' := E')
      (F := F) (F' := F') k) a₀ :=
  (cpolynomialAt_alternatingMapAction_of_split_destination k h a₀).analyticAt

/-- The joint action into a split pair is analytic everywhere. -/
theorem analyticOnNhd_alternatingMapAction_of_split_destination
    (k : ℕ) (h : IsSplitAlternatingPair K k E' F') :
    AnalyticOnNhd K (alternatingMapAction (K := K) (E := E) (E' := E')
      (F := F) (F' := F') k) Set.univ := by
  intro a₀ _
  exact analyticAt_alternatingMapAction_of_split_destination k h a₀

/-- Summary for a split destination: the lift `splitDestinationLift`, its formula and
diagonal, and polynomiality and analyticity of the joint action. -/
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
