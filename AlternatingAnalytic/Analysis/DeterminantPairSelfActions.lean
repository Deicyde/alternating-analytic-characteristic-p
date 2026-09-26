import AlternatingAnalytic.Analysis.DeterminantCrossActionObstruction
import AlternatingAnalytic.Analysis.DeterminantPairAllAlternating
import AlternatingAnalytic.Analysis.SplitAlternatingPairs

/-!
# The two unpadded analytic self-actions

This is the separate degree-p setup preceding the padded construction. Both
actions use the actual determinant-pair carriers and the original target G.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped BigOperators NNReal

namespace AlternatingAnalytic.DeterminantPair

variable (p : ℕ) [Fact p.Prime] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)]
attribute [local instance] preferredNormedFieldK preferredFieldK preferredFieldL

/-- The original rigid-source self-action, including actual postcomposition. -/
theorem unpadded_selfAction_eq
    (h : (E p r →L[K p r] E p r) × (G p r →L[K p r] G p r)) :
    alternatingMapAction p h =
      (RigidDenseSource.Concrete.endScalarEquiv p r h.1) ^ p •
        ContinuousLinearMap.compContinuousAlternatingMapCLM
          (K p r) (E p r) (G p r) (G p r) (Fin p) h.2 := by
  apply ContinuousLinearMap.ext
  intro m
  apply ContinuousAlternatingMap.ext
  intro x
  change h.2 (m (fun i => h.1 (x i))) = _
  simp_rw [RigidDenseSource.Concrete.endScalarEquiv_apply p r h.1]
  have hm : m (fun i => RigidDenseSource.Concrete.endScalarEquiv p r h.1 • x i) =
      (RigidDenseSource.Concrete.endScalarEquiv p r h.1) ^ p • m x := by
    simpa using m.toAlternatingMap.map_smul_univ
      (fun _ : Fin p => RigidDenseSource.Concrete.endScalarEquiv p r h.1) x
  rw [hm]
  simp

/-- The isometric scalar endomorphism coordinate as a bounded linear map. -/
def unpaddedScalarCoordinate : (E p r →L[K p r] E p r) →L[K p r] K p r :=
  (RigidDenseSource.Concrete.endScalarEquiv p r).toContinuousLinearEquiv.toContinuousLinearMap

/-- The actual bounded postcomposition operator with its normed type explicit. -/
def unpaddedPostcomposition : (G p r →L[K p r] G p r) →L[K p r]
    ((E p r [⋀^Fin p]→L[K p r] G p r) →L[K p r]
      (E p r [⋀^Fin p]→L[K p r] G p r)) :=
  ContinuousLinearMap.compContinuousAlternatingMapCLM
    (K p r) (E p r) (G p r) (G p r) (Fin p)

/-- The unpadded rigid-source action is analytic at every actual operator pair. -/
theorem analyticAt_unpaddedSelfActionE
    (h : (E p r →L[K p r] E p r) × (G p r →L[K p r] G p r)) :
    AnalyticAt (K p r)
      (alternatingMapAction (K := K p r) (E := E p r) (E' := E p r)
        (F := G p r) (F' := G p r) p) h := by
  let : IsBoundedSMul (K p r)
      ((E p r [⋀^Fin p]→L[K p r] G p r) →L[K p r]
        (E p r [⋀^Fin p]→L[K p r] G p r)) :=
    NormedSpace.toIsBoundedSMul (𝕜 := K p r)
      (E := (E p r [⋀^Fin p]→L[K p r] G p r) →L[K p r]
        (E p r [⋀^Fin p]→L[K p r] G p r))
  have hs := ((unpaddedScalarCoordinate p r).analyticAt h.1).comp analyticAt_fst
  have hp : AnalyticAt (K p r) (unpaddedPostcomposition p r) h.2 :=
    ContinuousLinearMap.analyticAt (𝕜 := K p r)
      (E := G p r →L[K p r] G p r)
      (F := (E p r [⋀^Fin p]→L[K p r] G p r) →L[K p r]
        (E p r [⋀^Fin p]→L[K p r] G p r)) (unpaddedPostcomposition p r) h.2
  have hv := hp.comp analyticAt_snd
  have ha := (hs.pow p).smul hv
  change AnalyticAt (K p r)
    (fun z : (E p r →L[K p r] E p r) × (G p r →L[K p r] G p r) =>
      (RigidDenseSource.Concrete.endScalarEquiv p r z.1) ^ p •
        ContinuousLinearMap.compContinuousAlternatingMapCLM
          (K p r) (E p r) (G p r) (G p r) (Fin p) z.2) h at ha
  have heq : (fun z : (E p r →L[K p r] E p r) × (G p r →L[K p r] G p r) =>
      (RigidDenseSource.Concrete.endScalarEquiv p r z.1) ^ p •
        ContinuousLinearMap.compContinuousAlternatingMapCLM
          (K p r) (E p r) (G p r) (G p r) (Fin p) z.2) =
      alternatingMapAction p := funext fun z => (unpadded_selfAction_eq p r z).symm
  rw [heq] at ha
  exact ha

/-- The original degree-p all-alternating inverse is the split witness. -/
theorem isSplit_unpaddedD : IsSplitAlternatingPair (K p r) p (D p r) (G p r) :=
  ⟨retractionR p r, retractionR_inclusionJ p r⟩

/-- The original determinant-source action is analytic at every operator pair. -/
theorem analyticAt_unpaddedSelfActionD
    (h : (D p r →L[K p r] D p r) × (G p r →L[K p r] G p r)) :
    AnalyticAt (K p r)
      (alternatingMapAction (K := K p r) (E := D p r) (E' := D p r)
        (F := G p r) (F' := G p r) p) h :=
  analyticAt_alternatingMapAction_of_split_destination p (isSplit_unpaddedD p r) h

/-- The separate degree-p source statement preceding the padded construction. -/
theorem unpadded_analytic_self_actions :
    (∀ h : (E p r →L[K p r] E p r) × (G p r →L[K p r] G p r),
      alternatingMapAction p h =
        (RigidDenseSource.Concrete.endScalarEquiv p r h.1) ^ p •
          ContinuousLinearMap.compContinuousAlternatingMapCLM
            (K p r) (E p r) (G p r) (G p r) (Fin p) h.2) ∧
    AnalyticOnNhd (K p r)
      (alternatingMapAction (K := K p r) (E := E p r) (E' := E p r)
        (F := G p r) (F' := G p r) p) Set.univ ∧
    (∀ m : D p r [⋀^Fin p]→L[K p r] G p r,
      retractionR p r m.toContinuousMultilinearMap = m) ∧
    IsSplitAlternatingPair (K p r) p (D p r) (G p r) ∧
    AnalyticOnNhd (K p r)
      (alternatingMapAction (K := K p r) (E := D p r) (E' := D p r)
        (F := G p r) (F' := G p r) p) Set.univ := by
  exact ⟨unpadded_selfAction_eq p r, fun h _ => analyticAt_unpaddedSelfActionE p r h,
    retractionR_inclusionJ p r, isSplit_unpaddedD p r,
    fun h _ => analyticAt_unpaddedSelfActionD p r h⟩

end AlternatingAnalytic.DeterminantPair
