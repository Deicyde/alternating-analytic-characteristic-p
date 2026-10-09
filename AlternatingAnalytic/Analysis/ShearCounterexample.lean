import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Analytic.Constructions
import AlternatingAnalytic.Main

/-!
# Invertible shears with nonanalytic pullback

On `D × E` with the maximum norm, the shear `g(u)(d, e) = (d + u e, e)` and its inverse `g(-u)`
are affine analytic in `u`. Extending forms along the first projection and restricting to the
second summand recovers `u ↦ u^*` from `u ↦ g(u)^*`, so the latter is not analytic where the
former is not. This is Proposition 6.4.
-/

noncomputable section

namespace AlternatingAnalytic

universe u

variable {K : Type u} [NontriviallyNormedField K]
  {D E F : Type*}
  [NormedAddCommGroup D] [NormedSpace K D]
  [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup F] [NormedSpace K F]

/-- The bounded linear part `u ↦ ((d, e) ↦ (u e, 0))` of the shear family. -/
def shearLinear : (E →L[K] D) →L[K] (D × E →L[K] D × E) :=
  ((ContinuousLinearMap.compL K (D × E) E (D × E)).flip
    (ContinuousLinearMap.snd K D E)).comp
    (ContinuousLinearMap.compL K E D (D × E) (ContinuousLinearMap.inl K D E))

@[simp]
theorem shearLinear_apply (u : E →L[K] D) (z : D × E) :
    shearLinear u z = (u z.2, 0) := rfl

/-- The affine shear family `g(u) = [[id, u], [0, id]]`. -/
def shear (u : E →L[K] D) : D × E →L[K] D × E :=
  ContinuousLinearMap.id K (D × E) + shearLinear u

@[simp]
theorem shear_apply (u : E →L[K] D) (z : D × E) :
    shear u z = (z.1 + u z.2, z.2) := by
  ext <;> simp [shear]

@[simp]
theorem shear_zero : shear (0 : E →L[K] D) = ContinuousLinearMap.id K (D × E) := by
  simp [shear]

@[simp]
theorem shear_neg_apply (u : E →L[K] D) (z : D × E) :
    shear (-u) (shear u z) = z := by
  ext <;> simp

@[simp]
theorem shear_apply_neg (u : E →L[K] D) (z : D × E) :
    shear u (shear (-u) z) = z := by
  ext <;> simp

/-- Every shear is a continuous linear automorphism, with inverse `shear (-u)`. -/
def shearEquiv (u : E →L[K] D) : (D × E) ≃L[K] (D × E) :=
  ContinuousLinearEquiv.equivOfInverse (shear u) (shear (-u))
    (shear_neg_apply u) (shear_apply_neg u)

@[simp]
theorem shearEquiv_toContinuousLinearMap (u : E →L[K] D) :
    (shearEquiv u).toContinuousLinearMap = shear u := rfl

@[simp]
theorem shearEquiv_symm_toContinuousLinearMap (u : E →L[K] D) :
    (shearEquiv u).symm.toContinuousLinearMap = shear (-u) := rfl

/-- The shear is affine analytic as an operator-valued family. -/
theorem analyticAt_shear (u₀ : E →L[K] D) : AnalyticAt K shear u₀ :=
  analyticAt_const.add (shearLinear.analyticAt u₀)

/-- The inverse family is affine, with linear part `-shearLinear`. -/
theorem shearEquiv_symm_eq_id_sub (u : E →L[K] D) :
    (shearEquiv u).symm.toContinuousLinearMap =
      ContinuousLinearMap.id K (D × E) - shearLinear u := by
  simp [shear, sub_eq_add_neg]

theorem analyticAt_shear_inverse (u₀ : E →L[K] D) :
    AnalyticAt K (fun u : E →L[K] D => (shearEquiv u).symm.toContinuousLinearMap) u₀ := by
  simp only [shearEquiv_symm_eq_id_sub]
  exact analyticAt_const.sub (shearLinear.analyticAt u₀)

variable {ι : Type*} [Fintype ι]

/-- Extend alternating forms on `D` along the first projection. -/
def shearExtend : (D [⋀^ι]→L[K] F) →L[K] ((D × E) [⋀^ι]→L[K] F) :=
  ContinuousAlternatingMap.compContinuousLinearMapCLM (ContinuousLinearMap.fst K D E)

/-- Restrict alternating forms on `D × E` to the second summand. -/
def shearRestrict : ((D × E) [⋀^ι]→L[K] F) →L[K] (E [⋀^ι]→L[K] F) :=
  ContinuousAlternatingMap.compContinuousLinearMapCLM (ContinuousLinearMap.inr K D E)

/-- The bounded linear map `T ↦ R ∘ T ∘ J` on spaces of operators on forms. -/
def shearCompression :
    (((D × E) [⋀^ι]→L[K] F) →L[K] ((D × E) [⋀^ι]→L[K] F)) →L[K]
      ((D [⋀^ι]→L[K] F) →L[K] (E [⋀^ι]→L[K] F)) :=
  (ContinuousLinearMap.compL K (D [⋀^ι]→L[K] F)
    ((D × E) [⋀^ι]→L[K] F) (E [⋀^ι]→L[K] F) shearRestrict).comp
    ((ContinuousLinearMap.compL K (D [⋀^ι]→L[K] F)
      ((D × E) [⋀^ι]→L[K] F) ((D × E) [⋀^ι]→L[K] F)).flip shearExtend)

/-- `R ∘ g(u)^* ∘ J = u^*`. -/
@[simp]
theorem shearCompression_pullback (u : E →L[K] D) :
    shearCompression (F := F) (ι := ι)
      (ContinuousAlternatingMap.compContinuousLinearMapCLM (shear u)) =
        ContinuousAlternatingMap.compContinuousLinearMapCLM u := by
  ext m x
  simp [shearCompression, shearRestrict, shearExtend, Function.comp_def]

/-- If `u ↦ u^*` is not analytic at `u₀`, neither is `u ↦ g(u)^*`. -/
theorem not_analyticAt_shear_pullback (u₀ : E →L[K] D)
    (h : ¬ AnalyticAt K
      (fun u : E →L[K] D =>
        (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
          (D [⋀^ι]→L[K] F) →L[K] (E [⋀^ι]→L[K] F))) u₀) :
    ¬ AnalyticAt K
      (fun u : E →L[K] D =>
        ContinuousAlternatingMap.compContinuousLinearMapCLM (F := F) (ι := ι)
          (shear u)) u₀ := by
  intro ha
  have hc := ContinuousLinearMap.analyticAt (𝕜 := K)
    (E := ((D × E) [⋀^ι]→L[K] F) →L[K] ((D × E) [⋀^ι]→L[K] F))
    (F := (D [⋀^ι]→L[K] F) →L[K] (E [⋀^ι]→L[K] F)) shearCompression
    (ContinuousAlternatingMap.compContinuousLinearMapCLM (shear u₀))
  have hQ := hc.comp (f := fun u : E →L[K] D =>
    ContinuousAlternatingMap.compContinuousLinearMapCLM (shear u)) ha
  apply h
  simpa only [Function.comp_def, shearCompression_pullback] using hQ

/-- The shear and its inverse are analytic, and `u ↦ g(u)^*` is not analytic at `u₀` when
`u ↦ u^*` is not. -/
theorem invertible_shear_counterexample (u₀ : E →L[K] D)
    (h : ¬ AnalyticAt K
      (fun u : E →L[K] D =>
        (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
          (D [⋀^ι]→L[K] F) →L[K] (E [⋀^ι]→L[K] F))) u₀) :
    AnalyticOnNhd K (fun u : E →L[K] D => (shearEquiv u).toContinuousLinearMap) Set.univ ∧
    AnalyticOnNhd K (fun u : E →L[K] D => (shearEquiv u).symm.toContinuousLinearMap)
      Set.univ ∧
    ¬ AnalyticAt K
      (fun u : E →L[K] D =>
        ContinuousAlternatingMap.compContinuousLinearMapCLM (F := F) (ι := ι)
          (shearEquiv u).toContinuousLinearMap) u₀ :=
  ⟨fun u _ => analyticAt_shear u, fun u _ => analyticAt_shear_inverse u,
    not_analyticAt_shear_pullback u₀ h⟩

/-- In characteristic `p` with `p ≤ k`, there are Banach spaces for which the shear family
through the identity is analytic with analytic inverse, but its action on alternating `k`-forms
is not analytic at `0`. -/
theorem exists_banach_shear_counterexample
    (K : Type u) [NontriviallyNormedField K] (p k : ℕ) (hp : p.Prime)
    [CharP K p] (hpk : p ≤ k) :
    ∃ (E F : Type u) (normedGroupE : NormedAddCommGroup E)
      (normedGroupF : NormedAddCommGroup F),
      let : NormedAddCommGroup E := normedGroupE
      let : NormedAddCommGroup F := normedGroupF
      ∃ (normedSpaceE : NormedSpace K E) (normedSpaceF : NormedSpace K F),
        let : NormedSpace K E := normedSpaceE
        let : NormedSpace K F := normedSpaceF
        ∃ (_ : CompleteSpace E) (_ : CompleteSpace F),
          shear (0 : E →L[K] E) = ContinuousLinearMap.id K (E × E) ∧
          AnalyticOnNhd K
            (fun v : E →L[K] E => (shearEquiv v).toContinuousLinearMap) Set.univ ∧
          AnalyticOnNhd K
            (fun v : E →L[K] E => (shearEquiv v).symm.toContinuousLinearMap) Set.univ ∧
          ¬ AnalyticAt K
            (fun v : E →L[K] E =>
              ContinuousAlternatingMap.compContinuousLinearMapCLM
                (F := F) (ι := Fin k) (shearEquiv v).toContinuousLinearMap)
            (0 : E →L[K] E) := by
  obtain ⟨E, F, gE, gF, nE, nF, cE, cF, _, hbad⟩ :=
    exists_nowhereAnalytic_banach_counterexample K p k hp hpk
  let : NormedAddCommGroup E := gE
  let : NormedAddCommGroup F := gF
  let : NormedSpace K E := nE
  let : NormedSpace K F := nF
  let : CompleteSpace E := cE
  let : CompleteSpace F := cF
  refine ⟨E, F, gE, gF, nE, nF, cE, cF, shear_zero, ?_⟩
  exact invertible_shear_counterexample (F := F) (ι := Fin k)
    (0 : E →L[K] E) (hbad (Fin k) (by simp) 0)

/-- Proposition 6.4 in full: formulas for the shear and its inverse, their analyticity, the
compression identity, transfer of nonanalyticity, and Banach witnesses in characteristic `p`
for `k ≥ p`. -/
theorem invertible_shear_transfer_full :
    (∀ (u : E →L[K] D) (z : D × E), shearEquiv u z = (z.1 + u z.2, z.2)) ∧
    (∀ u : E →L[K] D,
      (shearEquiv u).toContinuousLinearMap =
        ContinuousLinearMap.id K (D × E) + shearLinear u) ∧
    (∀ u : E →L[K] D, (shearEquiv u).symm.toContinuousLinearMap = shear (-u)) ∧
    (∀ u : E →L[K] D,
      (shearEquiv u).symm.toContinuousLinearMap =
        ContinuousLinearMap.id K (D × E) - shearLinear u) ∧
    (shearEquiv (0 : E →L[K] D)).toContinuousLinearMap =
      ContinuousLinearMap.id K (D × E) ∧
    AnalyticOnNhd K (fun u : E →L[K] D => (shearEquiv u).toContinuousLinearMap)
      Set.univ ∧
    AnalyticOnNhd K (fun u : E →L[K] D => (shearEquiv u).symm.toContinuousLinearMap)
      Set.univ ∧
    (∀ u : E →L[K] D,
      shearCompression (F := F) (ι := ι)
        (ContinuousAlternatingMap.compContinuousLinearMapCLM
          (shearEquiv u).toContinuousLinearMap) =
        ContinuousAlternatingMap.compContinuousLinearMapCLM u) ∧
    (∀ u₀ : E →L[K] D,
      (¬ AnalyticAt K
        (fun u : E →L[K] D =>
          (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
            (D [⋀^ι]→L[K] F) →L[K] (E [⋀^ι]→L[K] F))) u₀) →
      ¬ AnalyticAt K
        (fun u : E →L[K] D =>
          ContinuousAlternatingMap.compContinuousLinearMapCLM (F := F) (ι := ι)
            (shearEquiv u).toContinuousLinearMap) u₀) ∧
    (∀ (p k : ℕ), p.Prime → ∀ [CharP K p], p ≤ k →
      ∃ (E₀ F₀ : Type u) (normedGroupE : NormedAddCommGroup E₀)
        (normedGroupF : NormedAddCommGroup F₀),
        let : NormedAddCommGroup E₀ := normedGroupE
        let : NormedAddCommGroup F₀ := normedGroupF
        ∃ (normedSpaceE : NormedSpace K E₀) (normedSpaceF : NormedSpace K F₀),
          let : NormedSpace K E₀ := normedSpaceE
          let : NormedSpace K F₀ := normedSpaceF
          ∃ (_ : CompleteSpace E₀) (_ : CompleteSpace F₀),
            shear (0 : E₀ →L[K] E₀) = ContinuousLinearMap.id K (E₀ × E₀) ∧
            AnalyticOnNhd K
              (fun v : E₀ →L[K] E₀ => (shearEquiv v).toContinuousLinearMap) Set.univ ∧
            AnalyticOnNhd K
              (fun v : E₀ →L[K] E₀ => (shearEquiv v).symm.toContinuousLinearMap)
              Set.univ ∧
            ¬ AnalyticAt K
              (fun v : E₀ →L[K] E₀ =>
                ContinuousAlternatingMap.compContinuousLinearMapCLM
                  (F := F₀) (ι := Fin k) (shearEquiv v).toContinuousLinearMap)
              (0 : E₀ →L[K] E₀)) := by
  refine ⟨?_, ?_, shearEquiv_symm_toContinuousLinearMap, shearEquiv_symm_eq_id_sub,
    shear_zero, fun u _ => analyticAt_shear u, fun u _ => analyticAt_shear_inverse u,
    shearCompression_pullback, not_analyticAt_shear_pullback, ?_⟩
  · exact fun u z => shear_apply u z
  · exact fun _ => rfl
  · intro p k hp _ hpk
    exact exists_banach_shear_counterexample K p k hp hpk

end AlternatingAnalytic
