import AlternatingAnalytic.Forms.Calculus.AmbientDeriv

/-!
# Sheaf property, linear structure and pullbacks of ambient analytic forms

Part of Theorem 7.2. Ambient analyticity is local, compatible local forms glue, and it is
preserved by addition and scalar multiplication. For a `C^ω` map `h`, the pullback
`h^*η = (η ∘ h) ∘ (Dh, …, Dh)` is ambient analytic, since `j (h^*η)` is a bounded multilinear
expression in `j ∘ η ∘ h` and `Dh`. Pullback is functorial and commutes with `∧` and, by
Mathlib's `extDeriv_pullback`, with `d`.
-/

set_option maxSynthPendingDepth 3

open Filter Set
open scoped Topology ContDiff

namespace AlternatingAnalytic.Forms

variable {K : Type*} [NontriviallyNormedField K]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace K P]
  {P' : Type*} [NormedAddCommGroup P'] [NormedSpace K P']
  {P'' : Type*} [NormedAddCommGroup P''] [NormedSpace K P''] {k l : ℕ}

/-- Applying an analytic family of continuous linear maps to an analytic vector is analytic. -/
theorem analyticAt_clm_apply {X E F : Type*} [NormedAddCommGroup X] [NormedSpace K X]
    [NormedAddCommGroup E] [NormedSpace K E] [NormedAddCommGroup F] [NormedSpace K F]
    {L : X → E →L[K] F} {u : X → E} {x : X} (hL : AnalyticAt K L x) (hu : AnalyticAt K u x) :
    AnalyticAt K (fun z => L z (u z)) x := by
  have h := AnalyticAt.comp (f := fun z => (L z, u z)) (x := x)
    (ContinuousLinearMap.analyticAt_bilinear (ContinuousLinearMap.id K (E →L[K] F)) (L x, u x))
    (hL.prod hu)
  exact h

section Sheaf

/-- Ambient analyticity is local: it can be checked on open neighborhoods. -/
theorem isAmbientAnalyticOn_iff_local [CompleteSpace K] (η : P → P [⋀^Fin k]→L[K] K)
    (U : Set P) :
    IsAmbientAnalyticOn η U ↔
      ∀ y ∈ U, ∃ V : Set P, IsOpen V ∧ y ∈ V ∧ IsAmbientAnalyticOn η V := by
  refine ⟨fun h y hy => ⟨{x | AnalyticAt K (fun x => (η x).toContinuousMultilinearMap) x},
    isOpen_analyticAt _ _, h y hy, fun x hx => hx⟩, fun h y hy => ?_⟩
  obtain ⟨V, -, hyV, hV⟩ := h y hy
  exact hV y hyV

/-- Ambient analytic forms that agree on overlaps of an open family glue. -/
theorem exists_glue {ι : Type*} (V : ι → Set P) (hV : ∀ i, IsOpen (V i))
    (η : ι → P → P [⋀^Fin k]→L[K] K) (hη : ∀ i, IsAmbientAnalyticOn (η i) (V i))
    (hagree : ∀ i j, EqOn (η i) (η j) (V i ∩ V j)) :
    ∃ θ : P → P [⋀^Fin k]→L[K] K,
      IsAmbientAnalyticOn θ (⋃ i, V i) ∧ ∀ i, EqOn θ (η i) (V i) := by
  classical
  let θ : P → P [⋀^Fin k]→L[K] K := fun x =>
    if h : ∃ i, x ∈ V i then η h.choose x else 0
  have hθ : ∀ i, EqOn θ (η i) (V i) := by
    intro i x hx
    have h : ∃ i, x ∈ V i := ⟨i, hx⟩
    simp only [θ, h, ↓reduceDIte]
    exact hagree _ _ ⟨h.choose_spec, hx⟩
  refine ⟨θ, fun x hx => ?_, hθ⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  refine (hη i x hi).congr ?_
  filter_upwards [(hV i).mem_nhds hi] with z hz
  rw [hθ i hz]

end Sheaf

section Linear

/-- The zero form is ambient analytic. -/
theorem isAmbientAnalyticOn_zero (U : Set P) :
    IsAmbientAnalyticOn (fun _ : P => (0 : P [⋀^Fin k]→L[K] K)) U := fun _ _ => by
  simpa [IsAmbientAnalyticOn] using analyticAt_const

/-- Ambient analytic forms are closed under addition. -/
theorem IsAmbientAnalyticOn.add {U : Set P} {η ζ : P → P [⋀^Fin k]→L[K] K}
    (hη : IsAmbientAnalyticOn η U) (hζ : IsAmbientAnalyticOn ζ U) :
    IsAmbientAnalyticOn (fun y => η y + ζ y) U := fun y hy =>
  ((hη y hy).add (hζ y hy)).congr (Eventually.of_forall fun _ => rfl)

/-- Ambient analytic forms are closed under scalar multiplication. -/
theorem IsAmbientAnalyticOn.const_smul {U : Set P} (c : K) {η : P → P [⋀^Fin k]→L[K] K}
    (hη : IsAmbientAnalyticOn η U) :
    IsAmbientAnalyticOn (fun y => c • η y) U := fun y hy =>
  ((hη y hy).const_smul (c := c)).congr (Eventually.of_forall fun _ => rfl)

end Linear

section Pullback

/-- Pullback along the identity is the identity. -/
theorem pullback_id (η : P → P [⋀^Fin k]→L[K] K) : pullback (fun y : P => y) η = η := by
  funext y
  ext v
  simp [pullback, fderiv_fun_id]

/-- Pullback is contravariantly functorial on open sets where the maps are `C^ω`. -/
theorem pullback_comp {V : Set P''} {W : Set P'} (hV : IsOpen V) (hW : IsOpen W)
    {h₁ : P'' → P'} {h₂ : P' → P} (hh₁ : ContDiffOn K ω h₁ V) (hh₂ : ContDiffOn K ω h₂ W)
    (hmaps : MapsTo h₁ V W) (η : P → P [⋀^Fin k]→L[K] K) :
    EqOn (pullback (h₂ ∘ h₁) η) (pullback h₁ (pullback h₂ η)) V := by
  intro y hy
  have hd₁ : DifferentiableAt K h₁ y :=
    (hh₁.contDiffAt (hV.mem_nhds hy)).differentiableAt (by simp)
  have hd₂ : DifferentiableAt K h₂ (h₁ y) :=
    (hh₂.contDiffAt (hW.mem_nhds (hmaps hy))).differentiableAt (by simp)
  ext v
  simp only [pullback, fderiv_comp y hd₂ hd₁,
    ContinuousAlternatingMap.compContinuousLinearMap_apply,
    Function.comp_apply]
  rfl

/-- Pullback commutes with the wedge product. -/
theorem pullback_wedge (h : P' → P) (η : P → P [⋀^Fin k]→L[K] K)
    (ζ : P → P [⋀^Fin l]→L[K] K) :
    pullback h (fun y => wedge (η y) (ζ y)) =
      fun y => wedge (pullback h η y) (pullback h ζ y) := by
  funext y
  ext v
  exact (DFunLike.congr_fun (shuffle_compLinearMap (η (h y)).toAlternatingMap
    (ζ (h y)).toAlternatingMap (fderiv K h y : P' →ₗ[K] P)) v).symm

/-- Pullbacks of ambient analytic forms along `C^ω` maps are ambient analytic. -/
theorem IsAmbientAnalyticOn.pullback {U : Set P} {V : Set P'} (hV : IsOpen V) {h : P' → P}
    (hh : ContDiffOn K ω h V) (hmaps : MapsTo h V U) {η : P → P [⋀^Fin k]→L[K] K}
    (hη : IsAmbientAnalyticOn η U) :
    IsAmbientAnalyticOn (Forms.pullback h η) V := by
  intro y hy
  have hhy : AnalyticAt K h y := (hV.analyticOn_iff_analyticOnNhd.mp hh.analyticOn) y hy
  have hDh : AnalyticAt K (fderiv K h) y :=
    (hV.analyticOn_iff_analyticOnNhd.mp (hh.fderiv_of_isOpen hV le_top).analyticOn) y hy
  have h1 : AnalyticAt K (fun x => (η (h x)).toContinuousMultilinearMap) y :=
    (hη (h y) (hmaps hy)).comp hhy
  have h2 : AnalyticAt K (fun x =>
      ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
      K (fun _ : Fin k => P') (fun _ : Fin k => P) K (fun _ => fderiv K h x)) y :=
    (ContinuousMultilinearMap.analyticAt _).comp (AnalyticAt.pi fun _ => hDh)
  refine (analyticAt_clm_apply h2 h1).congr (Eventually.of_forall fun x => ?_)
  ext v
  rfl

/-- Pullback along a `C^ω` map commutes with the exterior derivative. -/
theorem pullback_extDeriv {U : Set P} {V : Set P'} (hV : IsOpen V)
    {h : P' → P} (hh : ContDiffOn K ω h V) (hmaps : MapsTo h V U)
    {η : P → P [⋀^Fin k]→L[K] K} (hη : IsAmbientAnalyticOn η U) :
    EqOn (extDeriv (Forms.pullback h η)) (Forms.pullback h (extDeriv η)) V := by
  intro y hy
  exact extDeriv_pullback (differentiableAt_of_analyticAt (hη (h y) (hmaps hy)))
    (hh.contDiffAt (hV.mem_nhds hy)) le_top

end Pullback

end AlternatingAnalytic.Forms
