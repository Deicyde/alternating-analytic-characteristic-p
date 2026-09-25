import AlternatingAnalytic.Analysis.AnalyticFamilies
import AlternatingAnalytic.Analysis.FactorialInvertible
import AlternatingAnalytic.Analysis.SphericalAnalytic
import Mathlib.Analysis.Calculus.ContDiff.ContinuousAlternatingMap
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

/-!
# Joint regularity of the alternating-map action

The action is smooth jointly in pullback and pushforward. A bounded multilinear
lift of pullback produces a lift of the joint action with one additional slot.
All degrees, including zero, and arbitrary normed source spaces are allowed.
-/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace AlternatingAnalytic

variable {K : Type*} [NontriviallyNormedField K]
  {E E' F F' : Type*}
  [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup E'] [NormedSpace K E']
  [NormedAddCommGroup F] [NormedSpace K F]
  [NormedAddCommGroup F'] [NormedSpace K F']

/-- Bounded bilinear postcomposition of a pullback operator by a target map. -/
def alternatingPostcompBilinear (k : ℕ) :
    (F →L[K] F') →L[K]
      ((E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F)) →L[K]
      ((E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F')) :=
  (ContinuousLinearMap.compL K _ _ _).comp
    (ContinuousLinearMap.compContinuousAlternatingMapCLM K E' F F' (Fin k))

@[simp]
theorem alternatingPostcompBilinear_apply (k : ℕ) (v : F →L[K] F')
    (T : (E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F)) :
    alternatingPostcompBilinear k v T =
      (ContinuousLinearMap.compContinuousAlternatingMapCLM K E' F F' (Fin k) v).comp T := rfl

theorem norm_alternatingPostcompBilinear_apply_le (k : ℕ) (v : F →L[K] F')
    (T : (E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F)) :
    ‖alternatingPostcompBilinear k v T‖ ≤ ‖v‖ * ‖T‖ := by
  apply (alternatingPostcompBilinear k v T).opNorm_le_bound (M := ‖v‖ * ‖T‖) (mul_nonneg (norm_nonneg v) (norm_nonneg T))
  intro m
  exact (v.norm_compContinuousAlternatingMap_le (T m)).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (T.le_opNorm m) (norm_nonneg v))

/-- The exact bounded-bilinear factorization of the joint action. -/
theorem alternatingMapAction_eq_bilinear (k : ℕ)
    (z : (E' →L[K] E) × (F →L[K] F')) :
    alternatingMapAction k z = alternatingPostcompBilinear k z.2
      (ContinuousAlternatingMap.compContinuousLinearMapCLM z.1) := rfl

theorem norm_alternatingMapAction_le (k : ℕ)
    (z : (E' →L[K] E) × (F →L[K] F')) :
    ‖alternatingMapAction k z‖ ≤ ‖z.2‖ * ‖z.1‖ ^ k := by
  apply (alternatingMapAction k z).opNorm_le_bound (mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _))
  intro m
  calc
    ‖alternatingMapAction k z m‖ ≤ ‖z.2‖ * ‖m.compContinuousLinearMap z.1‖ :=
      z.2.norm_compContinuousAlternatingMap_le _
    _ ≤ ‖z.2‖ * (‖m‖ * ‖z.1‖ ^ k) := by
      exact mul_le_mul_of_nonneg_left (by simpa using m.norm_compContinuousLinearMap_le z.1)
        (norm_nonneg _)
    _ = (‖z.2‖ * ‖z.1‖ ^ k) * ‖m‖ := by ring

/-- Smoothness transfer, including analytic order when supplied for pullback. -/
theorem contDiff_alternatingMapAction_of_precomposition (k : ℕ) {n : WithTop ℕ∞}
    (hQ : ContDiff K n (ContinuousAlternatingMap.compContinuousLinearMapCLM :
      (E' →L[K] E) → (E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F))) :
    ContDiff K n (alternatingMapAction (K := K) (E := E) (E' := E') (F := F) (F' := F') k) := by
  exact ((ContinuousLinearMap.compContinuousAlternatingMapCLM K E' F F' (Fin k)).contDiff.comp
    contDiff_snd).clm_comp (hQ.comp contDiff_fst)

/-- Joint smoothness for every finite order and for smooth order. -/
theorem contDiff_alternatingMapAction (k : ℕ) (n : ℕ∞) :
    ContDiff K n (alternatingMapAction (K := K) (E := E) (E' := E') (F := F) (F' := F') k) :=
  contDiff_alternatingMapAction_of_precomposition k
    ContinuousAlternatingMap.contDiff_compContinuousLinearMapCLM

@[simp]
theorem alternatingMapAction_id_right (k : ℕ) (u : E' →L[K] E) :
    alternatingMapAction k (u, ContinuousLinearMap.id K F) =
      ContinuousAlternatingMap.compContinuousLinearMapCLM u := by
  ext m x
  rfl

/-- The identity pushforward slice reflects joint analyticity to pullback. -/
theorem analyticAt_precomposition_of_analyticAt_alternatingMapAction
    (k : ℕ) (u₀ : E' →L[K] E)
    (h : AnalyticAt K (alternatingMapAction (F := F) (F' := F) k)
      (u₀, ContinuousLinearMap.id K F)) :
    AnalyticAt K (Round24Transfer.Q K (Fin k) E' E F) u₀ := by
  simpa only [Function.comp_def, alternatingMapAction_id_right] using
    h.comp (f := fun u : E' →L[K] E => (u, ContinuousLinearMap.id K F))
      (analyticAt_id.prod analyticAt_const)

-- Select the canonical operator norm explicitly for this nested operator space.
local instance alternatingPullbackLiftNorm (k : ℕ) :
    Norm (ContinuousMultilinearMap K (fun _ : Fin k => E' →L[K] E)
      ((E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F))) :=
  ContinuousMultilinearMap.hasOpNorm (𝕜 := K)
    (E := fun _ : Fin k => E' →L[K] E)
    (G := (E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F))

/-- A pullback lift with `k` slots becomes a joint lift with `k + 1` slots.
The last slot supplies pushforward and the first `k` slots supply pullback. -/
def alternatingMapActionLift (k : ℕ)
    (P : ContinuousMultilinearMap K (fun _ : Fin k => E' →L[K] E)
      ((E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F))) :
    ContinuousMultilinearMap K
      (fun _ : Fin (k + 1) => (E' →L[K] E) × (F →L[K] F'))
      ((E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F')) :=
by
  let B : ((E' →L[K] E) × (F →L[K] F')) →L[K]
      ((E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F)) →L[K]
      ((E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F')) :=
    (alternatingPostcompBilinear (K := K) (E := E) (E' := E') (F := F) (F' := F') k).comp
      (ContinuousLinearMap.snd K (E' →L[K] E) (F →L[K] F'))
  let Bflip : ((E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F)) →L[K]
      ((E' →L[K] E) × (F →L[K] F')) →L[K]
      ((E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F')) :=
    ContinuousLinearMap.flipₗᵢ K
      ((E' →L[K] E) × (F →L[K] F'))
      ((E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F))
      ((E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F')) B
  let Ppair : ContinuousMultilinearMap K
      (fun _ : Fin k => (E' →L[K] E) × (F →L[K] F'))
      ((E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F)) :=
    P.compContinuousLinearMap fun _ =>
      ContinuousLinearMap.fst K (E' →L[K] E) (F →L[K] F')
  let curried : ContinuousMultilinearMap K
      (fun _ : Fin k => (E' →L[K] E) × (F →L[K] F'))
      (((E' →L[K] E) × (F →L[K] F')) →L[K]
        ((E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F'))) :=
    Bflip.compContinuousMultilinearMap Ppair
  exact ContinuousMultilinearMap.uncurryRight (𝕜 := K)
    (G := (E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F'))
    (Ei := fun _ : Fin (k + 1) => (E' →L[K] E) × (F →L[K] F')) curried

@[simp]
theorem alternatingMapActionLift_apply (k : ℕ)
    (P : ContinuousMultilinearMap K (fun _ : Fin k => E' →L[K] E)
      ((E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F)))
    (z : Fin (k + 1) → (E' →L[K] E) × (F →L[K] F')) :
    alternatingMapActionLift k P z = alternatingPostcompBilinear k (z (Fin.last k)).2
      (P fun i => (z i.castSucc).1) := rfl

theorem norm_alternatingMapActionLift_apply_le (k : ℕ)
    (P : ContinuousMultilinearMap K (fun _ : Fin k => E' →L[K] E)
      ((E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F)))
    (z : Fin (k + 1) → (E' →L[K] E) × (F →L[K] F')) :
    ‖alternatingMapActionLift k P z‖ ≤ ‖P‖ * ∏ i, ‖z i‖ := by
  have hPbound := ContinuousMultilinearMap.le_opNorm_mul_prod_of_le (𝕜 := K)
      (E := fun _ : Fin k => E' →L[K] E)
      (G := (E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F)) P
      (m := fun i => (z i.castSucc).1) (b := fun i => ‖z i.castSucc‖)
      (fun i => norm_fst_le (z i.castSucc))
  rw [alternatingMapActionLift_apply]
  calc
    ‖alternatingPostcompBilinear k (z (Fin.last k)).2 (P fun i => (z i.castSucc).1)‖
        ≤ ‖(z (Fin.last k)).2‖ * ‖P fun i => (z i.castSucc).1‖ :=
      norm_alternatingPostcompBilinear_apply_le k _ _
    _ ≤ ‖z (Fin.last k)‖ * (‖P‖ * ∏ i : Fin k, ‖z i.castSucc‖) :=
      mul_le_mul (norm_snd_le (z (Fin.last k))) hPbound
        (norm_nonneg (P fun i => (z i.castSucc).1)) (norm_nonneg (z (Fin.last k)))
    _ = ‖P‖ * ∏ i, ‖z i‖ := by rw [Fin.prod_univ_castSucc]; ring

theorem alternatingMapActionLift_diag (k : ℕ)
    (P : ContinuousMultilinearMap K (fun _ : Fin k => E' →L[K] E)
      ((E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F)))
    (hP : ∀ u, P (fun _ => u) = ContinuousAlternatingMap.compContinuousLinearMapCLM u)
    (z : (E' →L[K] E) × (F →L[K] F')) :
    alternatingMapActionLift k P (fun _ => z) = alternatingMapAction k z := by
  rw [alternatingMapActionLift_apply, hP]
  rfl

theorem boundedLift_to_fin (k : ℕ)
    (h : Round24Transfer.HasBoundedLift K (Fin k) E' E F) :
    ∃ P : ContinuousMultilinearMap K (fun _ : Fin k => E' →L[K] E)
      ((E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F)),
      ∀ u, P (fun _ => u) = ContinuousAlternatingMap.compContinuousLinearMapCLM u := by
  obtain ⟨P, hP⟩ := h
  exact ⟨P.domDomCongr (Fintype.equivFin (Fin k)).symm, hP⟩
theorem boundedLift_of_fin (k : ℕ)
    (P : ContinuousMultilinearMap K (fun _ : Fin k => E' →L[K] E)
      ((E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F)))
    (hP : ∀ u, P (fun _ => u) = ContinuousAlternatingMap.compContinuousLinearMapCLM u) :
    Round24Transfer.HasBoundedLift K (Fin k) E' E F := by
  exact ⟨P.domDomCongr (Fintype.equivFin (Fin k)), hP⟩

/-- The global joint lift, including its formula, bound, and diagonal identity. -/
theorem exists_alternatingMapActionLift (k : ℕ)
    (h : Round24Transfer.HasBoundedLift K (Fin k) E' E F) :
    ∃ P : ContinuousMultilinearMap K (fun _ : Fin k => E' →L[K] E)
        ((E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F)),
      (∀ u, P (fun _ => u) = ContinuousAlternatingMap.compContinuousLinearMapCLM u) ∧
      ∃ L : ContinuousMultilinearMap K
          (fun _ : Fin (k + 1) => (E' →L[K] E) × (F →L[K] F'))
          ((E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F')),
        (∀ z, L z = alternatingPostcompBilinear k (z (Fin.last k)).2
          (P fun i => (z i.castSucc).1)) ∧
        (∀ z, ‖L z‖ ≤ ‖P‖ * ∏ i, ‖z i‖) ∧
        (∀ z, L (fun _ => z) = alternatingMapAction k z) := by
  obtain ⟨P, hP⟩ := boundedLift_to_fin k h
  refine ⟨P, hP, alternatingMapActionLift k P, alternatingMapActionLift_apply k P,
    norm_alternatingMapActionLift_apply_le k P, alternatingMapActionLift_diag k P hP⟩

/-- Finite polynomial regularity follows from the actual global joint lift. -/
theorem cpolynomialAt_alternatingMapAction_of_boundedLift (k : ℕ)
    (h : Round24Transfer.HasBoundedLift K (Fin k) E' E F)
    (z₀ : (E' →L[K] E) × (F →L[K] F')) :
    CPolynomialAt K (alternatingMapAction k) z₀ := by
  obtain ⟨P, hP, L, hL, hnorm, hdiag⟩ := exists_alternatingMapActionLift (F' := F') k h
  have heq : alternatingMapAction k = L ∘ (fun z => fun _ : Fin (k + 1) => z) :=
    funext fun z => (hdiag z).symm
  rw [heq]
  exact (ContinuousMultilinearMap.cpolynomialAt (𝕜 := K)
    (F := (E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F')) L).comp
    ((ContinuousLinearMap.pi fun _ : Fin (k + 1) =>
      ContinuousLinearMap.id K ((E' →L[K] E) × (F →L[K] F'))).cpolynomialAt z₀)

/-- Analytic pullback at the first coordinate gives joint analyticity, via its
bounded lift and the resulting finite polynomial joint action. -/
theorem analyticAt_alternatingMapAction_of_precomposition (k : ℕ)
    (z : (E' →L[K] E) × (F →L[K] F'))
    (hQ : AnalyticAt K (Round24Transfer.Q K (Fin k) E' E F) z.1) :
    AnalyticAt K (alternatingMapAction k) z :=
  (cpolynomialAt_alternatingMapAction_of_boundedLift k
    (Round24Transfer.hasBoundedLift_of_analyticAt hQ) z).analyticAt

/-- Invertibility of the factorial gives joint finite polynomial regularity. -/
theorem cpolynomialAt_alternatingMapAction_of_factorial_ne_zero (k : ℕ)
    (hk : (k.factorial : K) ≠ 0) (z₀ : (E' →L[K] E) × (F →L[K] F')) :
    CPolynomialAt K (alternatingMapAction k) z₀ := by
  apply cpolynomialAt_alternatingMapAction_of_boundedLift k
  apply Round24Transfer.hasBoundedLift_of_analyticAt (f₀ := (0 : E' →L[K] E))
  exact (ContinuousAlternatingMap.cpolynomialAt_compContinuousLinearMapCLM
    (by simpa using hk) _).analyticAt

/-- Spherical targets give joint finite polynomial regularity in every degree.
Neither source space is assumed ultrametric or complete. -/
theorem cpolynomialAt_alternatingMapAction_of_sphericallyComplete
    [IsUltrametricDist K] [IsUltrametricDist F] [SphericallyCompleteSpace F]
    (k : ℕ) (z₀ : (E' →L[K] E) × (F →L[K] F')) :
    CPolynomialAt K (alternatingMapAction k) z₀ :=
  cpolynomialAt_alternatingMapAction_of_boundedLift k
    ContinuousAlternatingMap.hasBoundedLift_of_sphericallyComplete z₀

/-- The operator-to-functor bridge in one concrete statement: the bilinear
factorization and its bounds, identity slice, unconditional joint smoothness,
and the formula, quantitative bound, diagonal identity and finite polynomial
consequence of every bounded pullback lift. -/
theorem alternatingMapAction_operator_bridge (k : ℕ) :
    (∀ z : (E' →L[K] E) × (F →L[K] F'),
      alternatingMapAction k z = alternatingPostcompBilinear k z.2
        (ContinuousAlternatingMap.compContinuousLinearMapCLM z.1)) ∧
    (∀ (v : F →L[K] F')
        (T : (E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F)),
      ‖alternatingPostcompBilinear k v T‖ ≤ ‖v‖ * ‖T‖) ∧
    (∀ z : (E' →L[K] E) × (F →L[K] F'),
      ‖alternatingMapAction k z‖ ≤ ‖z.2‖ * ‖z.1‖ ^ k) ∧
    (∀ u : E' →L[K] E,
      alternatingMapAction k (u, ContinuousLinearMap.id K F) =
        ContinuousAlternatingMap.compContinuousLinearMapCLM u) ∧
    (∀ n : ℕ∞, ContDiff K n
      (alternatingMapAction (K := K) (E := E) (E' := E') (F := F) (F' := F') k)) ∧
    (∀ u₀ : E' →L[K] E,
      AnalyticAt K (alternatingMapAction (F := F) (F' := F) k)
        (u₀, ContinuousLinearMap.id K F) →
      AnalyticAt K (Round24Transfer.Q K (Fin k) E' E F) u₀) ∧
    (∀ z : (E' →L[K] E) × (F →L[K] F'),
      AnalyticAt K (Round24Transfer.Q K (Fin k) E' E F) z.1 →
      AnalyticAt K (alternatingMapAction k) z) ∧
    (∀ P : ContinuousMultilinearMap K (fun _ : Fin k => E' →L[K] E)
        ((E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F)),
      (∀ u, P (fun _ => u) = ContinuousAlternatingMap.compContinuousLinearMapCLM u) →
      (∀ z : Fin (k + 1) → (E' →L[K] E) × (F →L[K] F'),
        alternatingMapActionLift k P z = alternatingPostcompBilinear k (z (Fin.last k)).2
          (P fun i => (z i.castSucc).1)) ∧
      (∀ z : Fin (k + 1) → (E' →L[K] E) × (F →L[K] F'),
        ‖alternatingMapActionLift k P z‖ ≤ ‖P‖ * ∏ i, ‖z i‖) ∧
      (∀ z : (E' →L[K] E) × (F →L[K] F'),
        alternatingMapActionLift k P (fun _ => z) = alternatingMapAction k z) ∧
      (∀ z₀ : (E' →L[K] E) × (F →L[K] F'),
        CPolynomialAt K (alternatingMapAction k) z₀)) := by
  refine ⟨alternatingMapAction_eq_bilinear k, norm_alternatingPostcompBilinear_apply_le k,
    norm_alternatingMapAction_le k, alternatingMapAction_id_right k,
    contDiff_alternatingMapAction k,
    analyticAt_precomposition_of_analyticAt_alternatingMapAction k,
    analyticAt_alternatingMapAction_of_precomposition k, ?_⟩
  intro P hP
  exact ⟨alternatingMapActionLift_apply k P, norm_alternatingMapActionLift_apply_le k P,
    alternatingMapActionLift_diag k P hP,
    cpolynomialAt_alternatingMapAction_of_boundedLift k
      (boundedLift_of_fin k P hP)⟩

end AlternatingAnalytic
