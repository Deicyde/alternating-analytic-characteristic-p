import AlternatingAnalytic.Analysis.AlternatingActionRegularity

/-!
# Universal alternating targets

Universal targets are defined by analyticity of the actual precomposition operator
for all normed spaces in the carrier universe of the field. The operator laws use
ordinary operator norms, in every degree, without completeness assumptions.
-/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

namespace AlternatingAnalytic

section Factorization

variable {K : Type*} [NontriviallyNormedField K]
  {E E' F F' : Type*}
  [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup E'] [NormedSpace K E']
  [NormedAddCommGroup F] [NormedSpace K F]
  [NormedAddCommGroup F'] [NormedSpace K F']

/-- Pull back first, then postcompose on the destination source space. -/
theorem alternatingMapAction_eq_source_precomposition (k : ℕ)
    (a : (E' →L[K] E) × (F →L[K] F')) :
    alternatingMapAction k a =
      (ContinuousLinearMap.compContinuousAlternatingMapCLM K E' F F' (Fin k) a.2).comp
        (ContinuousAlternatingMap.compContinuousLinearMapCLM a.1) := rfl

end Factorization

section TargetTransfer

variable {K : Type*} [NontriviallyNormedField K]
  {E E' F F' : Type*}
  [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup E'] [NormedSpace K E']
  [NormedAddCommGroup F] [NormedSpace K F]
  [NormedAddCommGroup F'] [NormedSpace K F']

/-- Postcompose first, then pull back with the destination target. -/
theorem alternatingMapAction_eq_target_precomposition (k : ℕ)
    (a : (E' →L[K] E) × (F →L[K] F')) :
    alternatingMapAction k a =
      (ContinuousAlternatingMap.compContinuousLinearMapCLM a.1).comp
        (ContinuousLinearMap.compContinuousAlternatingMapCLM K E F F' (Fin k) a.2) := by
  ext m x
  rfl

/-- Pointwise analytic target pullback gives joint analyticity by bounded bilinear composition. -/
theorem analyticAt_alternatingMapAction_of_target_precomposition
    (k : ℕ) (a₀ : (E' →L[K] E) × (F →L[K] F'))
    (hQ : AnalyticAt K
      (ContinuousAlternatingMap.compContinuousLinearMapCLM :
        (E' →L[K] E) →
          (E [⋀^Fin k]→L[K] F') →L[K] (E' [⋀^Fin k]→L[K] F')) a₀.1) :
    AnalyticAt K (alternatingMapAction (K := K) (E := E) (E' := E')
      (F := F) (F' := F') k) a₀ := by
  have h := (ContinuousLinearMap.analyticAt_bilinear
      (G := (E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F'))
      (ContinuousLinearMap.compL K
        (E [⋀^Fin k]→L[K] F) (E [⋀^Fin k]→L[K] F')
        (E' [⋀^Fin k]→L[K] F')) _).comp₂
    (hQ.comp analyticAt_fst)
    ((ContinuousLinearMap.analyticAt
      (F := (E [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F'))
      (ContinuousLinearMap.compContinuousAlternatingMapCLM K E F F' (Fin k)) _).comp
      analyticAt_snd)
  exact h.congr (Filter.Eventually.of_forall fun a =>
    (alternatingMapAction_eq_target_precomposition k a).symm)

private theorem cpolynomialAt_pair
    {P A B : Type*} [NormedAddCommGroup P] [NormedSpace K P]
    [NormedAddCommGroup A] [NormedSpace K A]
    [NormedAddCommGroup B] [NormedSpace K B]
    {f : P → A} {g : P → B} {x : P}
    (hf : CPolynomialAt K f x) (hg : CPolynomialAt K g x) :
    CPolynomialAt K (fun y => (f y, g y)) x := by
  have h := (((ContinuousLinearMap.inl K A B).cpolynomialAt (f x)).comp hf).add
    (((ContinuousLinearMap.inr K A B).cpolynomialAt (g x)).comp hg)
  change CPolynomialAt K (fun y => (f y, 0) + (0, g y)) x at h
  simpa only [Prod.mk_add_mk, add_zero, zero_add] using h

private theorem cpolynomialAt_bilinear
    {A B C : Type*} [NormedAddCommGroup A] [NormedSpace K A]
    [NormedAddCommGroup B] [NormedSpace K B]
    [NormedAddCommGroup C] [NormedSpace K C]
    (b : A →L[K] B →L[K] C) (x : A × B) :
    CPolynomialAt K (fun y : A × B => b y.1 y.2) x := by
  refine ⟨b.fpowerSeriesBilinear x, 3, ⊤, b.hasFPowerSeriesOnBall_bilinear x, ?_⟩
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm 3 m]
  exact b.fpowerSeriesBilinear_apply_add_three x m

/-- Pointwise finite-polynomial target pullback gives a finite-polynomial joint action. -/
theorem cpolynomialAt_alternatingMapAction_of_target_precomposition
    (k : ℕ) (a₀ : (E' →L[K] E) × (F →L[K] F'))
    (hQ : CPolynomialAt K
      (ContinuousAlternatingMap.compContinuousLinearMapCLM :
        (E' →L[K] E) →
          (E [⋀^Fin k]→L[K] F') →L[K] (E' [⋀^Fin k]→L[K] F')) a₀.1) :
    CPolynomialAt K (alternatingMapAction (K := K) (E := E) (E' := E')
      (F := F) (F' := F') k) a₀ := by
  have h := (cpolynomialAt_bilinear
      (C := (E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F'))
      (ContinuousLinearMap.compL K
      (E [⋀^Fin k]→L[K] F) (E [⋀^Fin k]→L[K] F')
      (E' [⋀^Fin k]→L[K] F')) _).comp
    (cpolynomialAt_pair
      (hQ.comp ((ContinuousLinearMap.fst K (E' →L[K] E) (F →L[K] F')).cpolynomialAt a₀))
      ((ContinuousLinearMap.cpolynomialAt
        (F := (E [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F'))
        (ContinuousLinearMap.compContinuousAlternatingMapCLM K E F F' (Fin k)) _).comp
        ((ContinuousLinearMap.snd K (E' →L[K] E) (F →L[K] F')).cpolynomialAt a₀)))
  exact h.congr (Filter.Eventually.of_forall fun a =>
    (alternatingMapAction_eq_target_precomposition k a).symm)

end TargetTransfer

section Transport

variable {K : Type*} [NontriviallyNormedField K]
  {E D F G : Type*}
  [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup D] [NormedSpace K D]
  [NormedAddCommGroup F] [NormedSpace K F]
  [NormedAddCommGroup G] [NormedSpace K G]

/-- The fixed bounded linear operator `T ↦ r_* ∘ T ∘ i_*` on pullback operators. -/
def alternatingTargetOperatorTransport (k : ℕ) (i : F →L[K] G) (r : G →L[K] F) :
    ((D [⋀^Fin k]→L[K] G) →L[K] (E [⋀^Fin k]→L[K] G)) →L[K]
      ((D [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F)) :=
  (ContinuousLinearMap.postcomp _
    (ContinuousLinearMap.compContinuousAlternatingMapCLM K E G F (Fin k) r)).comp
      (ContinuousLinearMap.precomp _
        (ContinuousLinearMap.compContinuousAlternatingMapCLM K D F G (Fin k) i))

@[simp]
theorem alternatingTargetOperatorTransport_apply (k : ℕ)
    (i : F →L[K] G) (r : G →L[K] F)
    (T : (D [⋀^Fin k]→L[K] G) →L[K] (E [⋀^Fin k]→L[K] G)) :
    alternatingTargetOperatorTransport k i r T =
      (ContinuousLinearMap.compContinuousAlternatingMapCLM K E G F (Fin k) r).comp
        (T.comp (ContinuousLinearMap.compContinuousAlternatingMapCLM K D F G (Fin k) i)) :=
  rfl

/-- A bounded retraction transports the actual pullback operator exactly. -/
theorem alternatingTargetOperatorTransport_precomposition (k : ℕ)
    (i : F →L[K] G) (r : G →L[K] F)
    (hri : r.comp i = ContinuousLinearMap.id K F) (u : E →L[K] D) :
    alternatingTargetOperatorTransport k i r
      (ContinuousAlternatingMap.compContinuousLinearMapCLM u) =
        ContinuousAlternatingMap.compContinuousLinearMapCLM u := by
  ext m x
  exact DFunLike.congr_fun hri (m fun j => u (x j))

end Transport

variable (K : Type u) [NontriviallyNormedField K]

/-- Analyticity of all pullback operators with this target. All carriers are in
`Type u`, the carrier universe used by `NormedSpaceCat K`. -/
def UniversalAlternatingTarget (k : ℕ) (F : Type u)
    [NormedAddCommGroup F] [NormedSpace K F] : Prop :=
  ∀ (E D : Type u) [NormedAddCommGroup E] [NormedSpace K E]
      [NormedAddCommGroup D] [NormedSpace K D],
    AnalyticOnNhd K
      (ContinuousAlternatingMap.compContinuousLinearMapCLM :
        (E →L[K] D) → (D [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F)) Set.univ

section Endpoints

variable {K} {E E' F F' : Type u}
  [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup E'] [NormedSpace K E']
  [NormedAddCommGroup F] [NormedSpace K F]
  [NormedAddCommGroup F'] [NormedSpace K F']

/-- A universal target at either endpoint gives joint analyticity of the action. -/
theorem analyticAt_alternatingMapAction_of_universal_target
    (k : ℕ) (a₀ : (E' →L[K] E) × (F →L[K] F'))
    (h : UniversalAlternatingTarget K k F ∨ UniversalAlternatingTarget K k F') :
    AnalyticAt K (alternatingMapAction (K := K) (E := E) (E' := E')
      (F := F) (F' := F') k) a₀ := by
  rcases h with h | h
  · exact analyticAt_alternatingMapAction_of_precomposition k a₀
      (h E' E a₀.1 (Set.mem_univ _))
  · exact analyticAt_alternatingMapAction_of_target_precomposition k a₀
      (h E' E a₀.1 (Set.mem_univ _))

/-- The joint action is analytic everywhere if either target is universal. -/
theorem analyticOnNhd_alternatingMapAction_of_universal_target
    (k : ℕ)
    (h : UniversalAlternatingTarget K k F ∨ UniversalAlternatingTarget K k F') :
    AnalyticOnNhd K (alternatingMapAction (K := K) (E := E) (E' := E')
      (F := F) (F' := F') k) Set.univ :=
  fun a₀ _ => analyticAt_alternatingMapAction_of_universal_target k a₀ h

end Endpoints

variable {K} {F G : Type u}
  [NormedAddCommGroup F] [NormedSpace K F]
  [NormedAddCommGroup G] [NormedSpace K G]

/-- Universal targets descend along arbitrary bounded linear retractions. -/
theorem UniversalAlternatingTarget.of_retract {k : ℕ}
    (i : F →L[K] G) (r : G →L[K] F)
    (hri : r.comp i = ContinuousLinearMap.id K F)
    (hG : UniversalAlternatingTarget K k G) : UniversalAlternatingTarget K k F := by
  intro E D _ _ _ _ u _
  have h := ((alternatingTargetOperatorTransport (E := E) (D := D) k i r).analyticAt
    (F := (D [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F))
    (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
      (D [⋀^Fin k]→L[K] G) →L[K] (E [⋀^Fin k]→L[K] G))).comp
        (hG E D u (Set.mem_univ u))
  simpa only [Function.comp_def,
    alternatingTargetOperatorTransport_precomposition k i r hri] using h

/-- Universal-target regularity is invariant under bounded linear isomorphism. -/
theorem universalAlternatingTarget_iff_of_continuousLinearEquiv
    (k : ℕ) (e : F ≃L[K] G) :
    UniversalAlternatingTarget K k F ↔ UniversalAlternatingTarget K k G := by
  constructor
  · intro h
    exact h.of_retract e.symm.toContinuousLinearMap e.toContinuousLinearMap (by ext; simp)
  · intro h
    exact h.of_retract e.toContinuousLinearMap e.symm.toContinuousLinearMap (by ext; simp)

/-- Finite max-norm products of universal targets are universal, including the empty product. -/
theorem UniversalAlternatingTarget.pi
    {I : Type u} [Fintype I] {Fi : I → Type u}
    [∀ i, NormedAddCommGroup (Fi i)] [∀ i, NormedSpace K (Fi i)]
    {k : ℕ} (h : ∀ i, UniversalAlternatingTarget K k (Fi i)) :
    UniversalAlternatingTarget K k (∀ i, Fi i) := by
  intro E D _ _ _ _ u₀ _
  let post (i : I) : (D [⋀^Fin k]→L[K] (∀ i, Fi i)) →L[K]
      (D [⋀^Fin k]→L[K] Fi i) :=
    ContinuousLinearMap.compContinuousAlternatingMapCLM K D (∀ i, Fi i) (Fi i)
      (Fin k) (ContinuousLinearMap.proj i)
  let trans (i : I) :
      ((D [⋀^Fin k]→L[K] Fi i) →L[K] (E [⋀^Fin k]→L[K] Fi i)) →L[K]
      ((D [⋀^Fin k]→L[K] (∀ i, Fi i)) →L[K] (E [⋀^Fin k]→L[K] Fi i)) :=
    (ContinuousLinearMap.compL K
      (D [⋀^Fin k]→L[K] (∀ i, Fi i)) (D [⋀^Fin k]→L[K] Fi i)
      (E [⋀^Fin k]→L[K] Fi i)).flip (post i)
  have hcoord (i : I) : AnalyticAt K
      (fun u : E →L[K] D =>
        (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
          (D [⋀^Fin k]→L[K] Fi i) →L[K] (E [⋀^Fin k]→L[K] Fi i)).comp
            (post i)) u₀ := by
    simpa only [Function.comp_def, trans, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.compL_apply] using ((trans i).analyticAt
      (F := (D [⋀^Fin k]→L[K] (∀ i, Fi i)) →L[K] (E [⋀^Fin k]→L[K] Fi i)) _).comp
        (h i E D u₀ (Set.mem_univ _))
  have hpi := AnalyticAt.pi hcoord
  let assemble := (ContinuousLinearMap.piEquivL K
    (D [⋀^Fin k]→L[K] (∀ i, Fi i))
    (fun i => E [⋀^Fin k]→L[K] Fi i)).toContinuousLinearMap
  have hassemble := (assemble.analyticAt
    (F := (D [⋀^Fin k]→L[K] (∀ i, Fi i)) →L[K]
      (∀ i, E [⋀^Fin k]→L[K] Fi i)) _).comp hpi
  let finish : (∀ i, E [⋀^Fin k]→L[K] Fi i) →L[K]
      (E [⋀^Fin k]→L[K] (∀ i, Fi i)) :=
    ContinuousLinearEquiv.toContinuousLinearMap
      (ContinuousAlternatingMap.piLIE K E (ι := Fin k) (F := Fi)).toContinuousLinearEquiv
  have hfinish :=
    ((ContinuousLinearMap.compL K
      (D [⋀^Fin k]→L[K] (∀ i, Fi i)) (∀ i, E [⋀^Fin k]→L[K] Fi i)
      (E [⋀^Fin k]→L[K] (∀ i, Fi i)) finish).analyticAt
        (F := (D [⋀^Fin k]→L[K] (∀ i, Fi i)) →L[K]
          (E [⋀^Fin k]→L[K] (∀ i, Fi i))) _).comp hassemble
  convert hfinish using 1
  ext u m x i
  rfl

/-- The operator part of `dom:core`: both exact factorizations, joint analyticity
from either universal endpoint, and closure under bounded retracts, bounded linear
isomorphisms, and finite products (including the empty product). -/
theorem universalAlternatingTarget_operator_laws (k : ℕ) :
    (∀ (E E' F F' : Type u)
      [NormedAddCommGroup E] [NormedSpace K E]
      [NormedAddCommGroup E'] [NormedSpace K E']
      [NormedAddCommGroup F] [NormedSpace K F]
      [NormedAddCommGroup F'] [NormedSpace K F']
      (a : (E' →L[K] E) × (F →L[K] F')),
      alternatingMapAction k a =
        (ContinuousLinearMap.compContinuousAlternatingMapCLM K E' F F' (Fin k) a.2).comp
          (ContinuousAlternatingMap.compContinuousLinearMapCLM a.1) ∧
      alternatingMapAction k a =
        (ContinuousAlternatingMap.compContinuousLinearMapCLM a.1).comp
          (ContinuousLinearMap.compContinuousAlternatingMapCLM K E F F' (Fin k) a.2) ∧
      ((UniversalAlternatingTarget K k F ∨ UniversalAlternatingTarget K k F') →
        AnalyticAt K (alternatingMapAction k) a)) ∧
    (∀ (F G : Type u) [NormedAddCommGroup F] [NormedSpace K F]
      [NormedAddCommGroup G] [NormedSpace K G]
      (i : F →L[K] G) (r : G →L[K] F),
      r.comp i = ContinuousLinearMap.id K F →
        UniversalAlternatingTarget K k G → UniversalAlternatingTarget K k F) ∧
    (∀ (F G : Type u) [NormedAddCommGroup F] [NormedSpace K F]
      [NormedAddCommGroup G] [NormedSpace K G] (_e : F ≃L[K] G),
      UniversalAlternatingTarget K k F ↔ UniversalAlternatingTarget K k G) ∧
    (∀ (I : Type u) [Fintype I] (Fi : I → Type u)
      [∀ i, NormedAddCommGroup (Fi i)] [∀ i, NormedSpace K (Fi i)],
      (∀ i, UniversalAlternatingTarget K k (Fi i)) →
        UniversalAlternatingTarget K k (∀ i, Fi i)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro E E' F F' _ _ _ _ _ _ _ _ a
    exact ⟨alternatingMapAction_eq_source_precomposition k a,
      alternatingMapAction_eq_target_precomposition k a,
      analyticAt_alternatingMapAction_of_universal_target k a⟩
  · intro F G _ _ _ _ i r hri hG
    exact hG.of_retract i r hri
  · intro F G _ _ _ _ e
    exact universalAlternatingTarget_iff_of_continuousLinearEquiv k e
  · intro I _ Fi _ _ h
    exact UniversalAlternatingTarget.pi h

end AlternatingAnalytic
