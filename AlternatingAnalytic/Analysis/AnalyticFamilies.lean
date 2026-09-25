import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Analytic.Constructions

/-!
# Analytic families of alternating-map morphisms

This file proves the family structure of `paper/charp.tex`, Proposition
`fam:prop:category`: constants, analytic reparameterization, local gluing,
composition with common or independent parameters, and the largest-collection
property. It also gives the equivalent analytic graph-lift characterization.

A morphism from `(E, F)` to `(E', F')` is a pair in
`(E' →L[K] E) × (F →L[K] F')`, with the usual maximum product norm.
Families are represented by ambient functions and `AnalyticOnNhd` on their
parameter domains. On open domains the predicate depends only on the restriction.
No completeness, characteristic, or finite-dimensionality assumptions are needed.
The subsequent scalar-family, addition-obstruction, ambient-polynomial, and
reflection results in the manuscript are outside this file's scope.
-/

noncomputable section

namespace AlternatingAnalytic

variable {K : Type*} [NontriviallyNormedField K]
  {E E' E'' F F' F'' P Q : Type*}
  [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup E'] [NormedSpace K E']
  [NormedAddCommGroup E''] [NormedSpace K E'']
  [NormedAddCommGroup F] [NormedSpace K F]
  [NormedAddCommGroup F'] [NormedSpace K F']
  [NormedAddCommGroup F''] [NormedSpace K F'']
  [NormedAddCommGroup P] [NormedSpace K P]
  [NormedAddCommGroup Q] [NormedSpace K Q]

/-- The joint action `m ↦ v ∘ m ∘ (u, …, u)` on continuous alternating maps. -/
def alternatingMapAction (k : ℕ) (h : (E' →L[K] E) × (F →L[K] F')) :
    (E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F') :=
  (ContinuousLinearMap.compContinuousAlternatingMapCLM K E' F F' (Fin k) h.2).comp
    (ContinuousAlternatingMap.compContinuousLinearMapCLM h.1)

@[simp]
theorem alternatingMapAction_apply (k : ℕ) (h : (E' →L[K] E) × (F →L[K] F'))
    (m : E [⋀^Fin k]→L[K] F) (x : Fin k → E') :
    alternatingMapAction k h m x = h.2 (m fun i => h.1 (x i)) := rfl

/-- Composition of morphism pairs, contravariant in their first component. -/
def alternatingMorphismComp (g : (E'' →L[K] E') × (F' →L[K] F''))
    (h : (E' →L[K] E) × (F →L[K] F')) :
    (E'' →L[K] E) × (F →L[K] F'') := (h.1.comp g.1, g.2.comp h.2)

@[simp]
theorem alternatingMapAction_comp (k : ℕ)
    (g : (E'' →L[K] E') × (F' →L[K] F''))
    (h : (E' →L[K] E) × (F →L[K] F')) :
    alternatingMapAction k (alternatingMorphismComp g h) =
      (alternatingMapAction k g).comp (alternatingMapAction k h) := by
  ext m x
  rfl

@[simp]
theorem alternatingMapAction_id (k : ℕ) :
    alternatingMapAction k (ContinuousLinearMap.id K E, ContinuousLinearMap.id K F) =
      ContinuousLinearMap.id K (E [⋀^Fin k]→L[K] F) := by
  ext m x
  rfl

/-- An admissible family is analytic both as a morphism pair and in its induced
action on alternating maps (Definition `fam:def:admissible`). -/
def IsAdmissibleOn (k : ℕ) (γ : P → (E' →L[K] E) × (F →L[K] F')) (s : Set P) : Prop :=
  AnalyticOnNhd K γ s ∧ AnalyticOnNhd K (alternatingMapAction k ∘ γ) s

private theorem analyticOnNhd_clm_comp {s : Set P}
    {g : P → E' →L[K] E''} {f : P → E →L[K] E'}
    (hg : AnalyticOnNhd K g s) (hf : AnalyticOnNhd K f s) :
    AnalyticOnNhd K (fun x => (g x).comp (f x)) s := by
  intro x hx
  exact ((ContinuousLinearMap.compL K E E' E'').analyticAt_bilinear _).comp₂
    (hg x hx) (hf x hx)

namespace IsAdmissibleOn

variable {k : ℕ} {s : Set P} {t : Set Q}
  {γ δ : P → (E' →L[K] E) × (F →L[K] F')}

/-- Every individual morphism defines a constant admissible family. -/
theorem const (h : (E' →L[K] E) × (F →L[K] F')) :
    IsAdmissibleOn k (fun _ : P => h) s :=
  ⟨analyticOnNhd_const, analyticOnNhd_const⟩

/-- Restriction preserves admissibility. -/
theorem mono (hγ : IsAdmissibleOn k γ s) {u : Set P} (hu : u ⊆ s) :
    IsAdmissibleOn k γ u :=
  ⟨hγ.1.mono hu, hγ.2.mono hu⟩

/-- On an open domain, admissibility depends only on the values on that domain. -/
theorem congr (hγ : IsAdmissibleOn k γ s) (hs : IsOpen s) (h : s.EqOn γ δ) :
    IsAdmissibleOn k δ s :=
  ⟨hγ.1.congr hs h, hγ.2.congr hs (fun _ hx => congrArg (alternatingMapAction k) (h hx))⟩

/-- Admissibility is preserved by analytic reparameterization. -/
theorem reparam (hγ : IsAdmissibleOn k γ s) {f : Q → P}
    (hf : AnalyticOnNhd K f t) (hfs : Set.MapsTo f t s) :
    IsAdmissibleOn k (γ ∘ f) t :=
  ⟨hγ.1.comp hf hfs, hγ.2.comp hf hfs⟩

/-- Local gluing: a family agreeing locally with admissible families is admissible.
In particular, this applies to a glued function on any open cover. -/
theorem of_locally
    (h : ∀ x ∈ s, ∃ u : Set P, IsOpen u ∧ x ∈ u ∧
      ∃ δ : P → (E' →L[K] E) × (F →L[K] F'),
        IsAdmissibleOn k δ u ∧ u.EqOn δ γ) :
    IsAdmissibleOn k γ s := by
  have hx (x : P) (hxs : x ∈ s) :
      AnalyticAt K γ x ∧ AnalyticAt K (alternatingMapAction k ∘ γ) x := by
    obtain ⟨u, hu, hxu, δ, hδ, heq⟩ := h x hxs
    exact ⟨(hδ.congr hu heq).1 x hxu, (hδ.congr hu heq).2 x hxu⟩
  exact ⟨fun x hxs => (hx x hxs).1, fun x hxs => (hx x hxs).2⟩

/-- Categorical composition of admissible families with a common parameter. -/
theorem comp {η : P → (E'' →L[K] E') × (F' →L[K] F'')}
    (hη : IsAdmissibleOn k η s) (hγ : IsAdmissibleOn k γ s) :
    IsAdmissibleOn k (fun x => alternatingMorphismComp (η x) (γ x)) s := by
  constructor
  · exact (analyticOnNhd_clm_comp
      (fun x hx => analyticAt_fst.comp (hγ.1 x hx))
      (fun x hx => analyticAt_fst.comp (hη.1 x hx))).prod
      (analyticOnNhd_clm_comp
        (fun x hx => analyticAt_snd.comp (hη.1 x hx))
        (fun x hx => analyticAt_snd.comp (hγ.1 x hx)))
  · simpa only [Function.comp_def, alternatingMapAction_comp] using
      analyticOnNhd_clm_comp hη.2 hγ.2

/-- Categorical composition also allows independent parameter spaces. -/
theorem comp_prod {η : Q → (E'' →L[K] E') × (F' →L[K] F'')}
    (hη : IsAdmissibleOn k η t) (hγ : IsAdmissibleOn k γ s) :
    IsAdmissibleOn k
      (fun x : P × Q => alternatingMorphismComp (η x.2) (γ x.1)) (s ×ˢ t) :=
  (hη.reparam analyticOnNhd_snd (fun _ hx => hx.2)).comp
    (hγ.reparam analyticOnNhd_fst (fun _ hx => hx.1))

end IsAdmissibleOn

/-- A family is admissible exactly when its lift to the ambient graph product is
analytic. This places no manifold or normed-space structure on the graph itself. -/
theorem isAdmissibleOn_iff_graph (k : ℕ)
    (γ : P → (E' →L[K] E) × (F →L[K] F')) (s : Set P) :
    IsAdmissibleOn k γ s ↔
      AnalyticOnNhd K (fun x => (γ x, alternatingMapAction k (γ x))) s := by
  constructor
  · intro h
    exact h.1.prod h.2
  · intro h
    exact ⟨fun x hx => analyticAt_fst.comp (h x hx),
      fun x hx => analyticAt_snd.comp (h x hx)⟩

/-- Every collection of ordinary analytic families whose alternating-map actions
are analytic is contained in the admissible families. Together with the two
defining projections, this is the largest-collection assertion. -/
theorem isAdmissibleOn_largest (k : ℕ) (s : Set P)
    (C : Set (P → (E' →L[K] E) × (F →L[K] F')))
    (hC : ∀ γ ∈ C, AnalyticOnNhd K γ s)
    (hA : ∀ γ ∈ C, AnalyticOnNhd K (alternatingMapAction k ∘ γ) s) :
    C ⊆ {γ | IsAdmissibleOn k γ s} :=
  fun γ hγ => ⟨hC γ hγ, hA γ hγ⟩

end AlternatingAnalytic
