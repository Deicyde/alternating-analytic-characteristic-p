import AlternatingAnalytic.Main
import AlternatingAnalytic.Analysis.L1BanachQuotient
import AlternatingAnalytic.Analysis.L1Families
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# Analyticity does not descend through ℓ¹ quotient parameters

Let `q : ℓ¹(J) → H` be the closed-unit-ball quotient onto `H = E →L[K] E`. Alternating
precomposition `Q` composed with `q` is analytic, but for the Banach counterexample of
Theorem 6.1(1) (`AlternatingAnalytic.Main`), `Q` is nowhere analytic. Hence no local section of `q` is differentiable at any point
(its derivative would split `q`), and `H` is not a bounded linear retract of any `ℓ¹(I)`.

A section on an open `U` is encoded as a total map `s : H → ℓ¹` satisfying `q (s h) = h` on `U`.
-/

noncomputable section

open Filter Topology
open L1Coordinates (L1)

universe u v uK uE uF

namespace AlternatingAnalytic

section LocalSections

variable {K X H Y : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup X] [NormedSpace K X]
  [NormedAddCommGroup H] [NormedSpace K H]
  [NormedAddCommGroup Y] [NormedSpace K Y]

/-- A local section differentiable at one point yields a bounded linear right inverse. -/
theorem rightInverse_fderiv_of_local_section
    (q : X →L[K] H) {s : H → X} {h₀ : H}
    (hs : DifferentiableAt K s h₀)
    (hsection : ∀ᶠ h in 𝓝 h₀, q (s h) = h) :
    q.comp (fderiv K s h₀) = ContinuousLinearMap.id K H := by
  have hcomp := (q.hasFDerivAt).comp h₀ hs.hasFDerivAt
  have hid : HasFDerivAt (fun h : H => h) (q.comp (fderiv K s h₀)) h₀ :=
    hcomp.congr_of_eventuallyEq (Filter.EventuallyEq.symm hsection)
  exact hid.unique (hasFDerivAt_id h₀)

/-- Analyticity after a bounded linear map descends through a bounded linear right inverse. -/
theorem analyticOnNhd_of_comp_rightInverse
    (q : X →L[K] H) (r : H →L[K] X)
    (hqr : q.comp r = ContinuousLinearMap.id K H)
    {f : H → Y} (hf : AnalyticOnNhd K (f ∘ q) Set.univ) :
    AnalyticOnNhd K f Set.univ := by
  have hcomp : (f ∘ q) ∘ r = f := by
    funext h
    have heq : q (r h) = h := DFunLike.congr_fun hqr h
    exact congrArg f heq
  intro h _
  rw [← hcomp]
  exact (hf (r h) (Set.mem_univ _)).comp (r.analyticAt h)

/-- If `f ∘ q` is analytic but `f` is not analytic somewhere, no local section of `q` is
differentiable at its base point. -/
theorem not_differentiableAt_of_local_section
    (q : X →L[K] H) {f : H → Y}
    (hf : AnalyticOnNhd K (f ∘ q) Set.univ)
    {h : H} (hnot : ¬AnalyticAt K f h)
    {s : H → X} {h₀ : H}
    (hsection : ∀ᶠ h in 𝓝 h₀, q (s h) = h) :
    ¬DifferentiableAt K s h₀ := by
  intro hs
  have hqr := rightInverse_fderiv_of_local_section q hs hsection
  exact hnot (analyticOnNhd_of_comp_rightInverse q (fderiv K s h₀) hqr hf h
    (Set.mem_univ _))

/-- The same for a section on an open set `U`, encoded as a total map. -/
theorem not_differentiableAt_section_of_isOpen
    (q : X →L[K] H) {f : H → Y}
    (hf : AnalyticOnNhd K (f ∘ q) Set.univ)
    {h : H} (hnot : ¬AnalyticAt K f h)
    {U : Set H} (hU : IsOpen U) {s : H → X}
    (hsection : ∀ h ∈ U, q (s h) = h) {h₀ : H} (hh₀ : h₀ ∈ U) :
    ¬DifferentiableAt K s h₀ := by
  apply not_differentiableAt_of_local_section q hf hnot
  exact Filter.eventually_of_mem (hU.mem_nhds hh₀) hsection

/-- The same with differentiability within `U`. -/
theorem not_differentiableWithinAt_section_of_isOpen
    (q : X →L[K] H) {f : H → Y}
    (hf : AnalyticOnNhd K (f ∘ q) Set.univ)
    {h : H} (hnot : ¬AnalyticAt K f h)
    {U : Set H} (hU : IsOpen U) {s : H → X}
    (hsection : ∀ h ∈ U, q (s h) = h) {h₀ : H} (hh₀ : h₀ ∈ U) :
    ¬DifferentiableWithinAt K s U h₀ := by
  intro hs
  exact not_differentiableAt_section_of_isOpen q hf hnot hU hsection hh₀
    (hs.differentiableAt (hU.mem_nhds hh₀))


end LocalSections

section L1Precomposition

variable {K : Type uK} [NontriviallyNormedField K]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace K E]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace K F]

/-- The action of `(u, id)` is alternating precomposition by `u`. -/
@[simp]
theorem alternatingMapAction_pair_id_eq_Q (k : ℕ) (u : E →L[K] E) :
    alternatingMapAction k (u, ContinuousLinearMap.id K F) =
      LiftCriterion.Q K (Fin k) E E F u := by
  ext m x
  rfl

/-- A bounded linear map from `ℓ¹(I)` gives an admissible precomposition family, for an
index type `I` in any universe. -/
theorem isAdmissibleOn_l1_precomposition [CompleteSpace F] (k : ℕ) {I : Type v}
    (r : L1 K I →L[K] (E →L[K] E)) :
    IsAdmissibleOn k (fun a => (r a, ContinuousLinearMap.id K F)) Set.univ := by
  exact isAdmissibleOn_of_l1 k ((r.analyticOnNhd Set.univ).prod analyticOnNhd_const)

/-- Alternating precomposition composed with a bounded linear map from `ℓ¹(I)` is analytic. -/
theorem analyticOnNhd_Q_comp_l1 [CompleteSpace F] (k : ℕ) {I : Type v}
    (r : L1 K I →L[K] (E →L[K] E)) :
    AnalyticOnNhd K (LiftCriterion.Q K (Fin k) E E F ∘ r) Set.univ := by
  simpa only [Function.comp_def, alternatingMapAction_pair_id_eq_Q] using
    (isAdmissibleOn_l1_precomposition (F := F) k r).2

/-- If `Q` is nowhere analytic, `E →L[K] E` is not a bounded linear retract of any `ℓ¹(I)`. -/
theorem no_l1_retract_of_nowhere_analytic_Q [CompleteSpace F] (k : ℕ)
    (hQ : ∀ h : E →L[K] E, ¬AnalyticAt K (LiftCriterion.Q K (Fin k) E E F) h)
    (I : Type v) (i : (E →L[K] E) →L[K] L1 K I)
    (r : L1 K I →L[K] (E →L[K] E)) :
    r.comp i ≠ ContinuousLinearMap.id K (E →L[K] E) := by
  intro hri
  have hri_apply (h : E →L[K] E) : r (i h) = h := DFunLike.congr_fun hri h
  have hcomp : (LiftCriterion.Q K (Fin k) E E F ∘ r) ∘ i =
      LiftCriterion.Q K (Fin k) E E F := by
    funext h
    exact congrArg (LiftCriterion.Q K (Fin k) E E F) (hri_apply h)
  have h := ((analyticOnNhd_Q_comp_l1 (F := F) k r) (i 0) (Set.mem_univ _)).comp
    (i.analyticAt 0)
  rw [hcomp] at h
  exact hQ 0 h


end L1Precomposition

section Counterexample

variable (K E F : Type*) [NontriviallyNormedField K]
  [NormedAddCommGroup E] [NormedSpace K E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace K F] [CompleteSpace F]

/-- If `Q` is nowhere analytic, the unit-ball quotient `q` has analytic pullback `Q ∘ q`, no
local section differentiable at any point, and `H` is not a retract of any `ℓ¹(I)`. -/
theorem quotient_parameter_counterexample_of_nowhereAnalytic (k : ℕ)
    (hQ : ∀ h : E →L[K] E, ¬AnalyticAt K (LiftCriterion.Q K (Fin k) E E F) h) :
    let H := E →L[K] E
    let J := L1UnitBallIndex H
    let q := unitBallL1Quotient K H
    let Q := LiftCriterion.Q K (Fin k) E E F
    ‖q‖ ≤ 1 ∧ Function.Surjective q ∧ IsOpenMap q ∧
    AnalyticOnNhd K (Q ∘ q) Set.univ ∧
    (∀ h : H, ¬AnalyticAt K Q h) ∧
    (∀ (U : Set H), IsOpen U → ∀ s : H → lp (fun _ : J => K) 1,
      (∀ h ∈ U, q (s h) = h) → ∀ h₀ ∈ U, ¬DifferentiableAt K s h₀) ∧
    (∀ (I : Type v) (i : H →L[K] lp (fun _ : I => K) 1)
      (r : lp (fun _ : I => K) 1 →L[K] H),
      r.comp i ≠ ContinuousLinearMap.id K H) := by
  have hup := analyticOnNhd_Q_comp_l1 (F := F) k
    (unitBallL1Quotient K (E →L[K] E))
  refine ⟨norm_unitBallL1Quotient_le, unitBallL1Quotient_surjective,
    unitBallL1Quotient_isOpenMap, hup, hQ, ?_, ?_⟩
  · intro U hU s hs h₀ hh₀
    exact not_differentiableAt_section_of_isOpen
      (unitBallL1Quotient K (E →L[K] E)) hup (hQ 0) hU hs hh₀
  · exact no_l1_retract_of_nowhere_analytic_Q k hQ

end Counterexample

/-- Over a complete field of characteristic `p > 0` with `p ≤ k`, there are Banach spaces for
which analyticity fails to descend through the unit-ball quotient, and `E →L[K] E` is not a
retract of any `ℓ¹(I)`. -/
theorem exists_quotient_parameter_counterexample
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K]
    (p k : ℕ) [CharP K p] (hp : 0 < p) (hpk : p ≤ k) :
    ∃ (E F : Type u) (normedGroupE : NormedAddCommGroup E)
      (normedGroupF : NormedAddCommGroup F),
      let : NormedAddCommGroup E := normedGroupE
      let : NormedAddCommGroup F := normedGroupF
      ∃ (normedSpaceE : NormedSpace K E) (normedSpaceF : NormedSpace K F),
        let : NormedSpace K E := normedSpaceE
        let : NormedSpace K F := normedSpaceF
        ∃ (_ : CompleteSpace E) (_ : CompleteSpace F),
          let H := E →L[K] E
          let J := L1UnitBallIndex H
          let q := unitBallL1Quotient K H
          let Q := LiftCriterion.Q K (Fin k) E E F
          ‖q‖ ≤ 1 ∧ Function.Surjective q ∧ IsOpenMap q ∧
          AnalyticOnNhd K (Q ∘ q) Set.univ ∧
          (∀ h : H, ¬AnalyticAt K Q h) ∧
          (∀ (U : Set H), IsOpen U → ∀ s : H → lp (fun _ : J => K) 1,
            (∀ h ∈ U, q (s h) = h) → ∀ h₀ ∈ U, ¬DifferentiableAt K s h₀) ∧
          (∀ (I : Type v) (i : H →L[K] lp (fun _ : I => K) 1)
            (r : lp (fun _ : I => K) 1 →L[K] H),
            r.comp i ≠ ContinuousLinearMap.id K H) := by
  have hprime : p.Prime := CharP.char_prime_of_ne_zero K (Nat.ne_of_gt hp)
  obtain ⟨E, F, gE, gF, nE, nF, cE, cF, _, hQ⟩ :=
    exists_nowhereAnalytic_banach_counterexample.{u, 0} K p k hprime hpk
  let : NormedAddCommGroup E := gE
  let : NormedAddCommGroup F := gF
  let : NormedSpace K E := nE
  let : NormedSpace K F := nF
  let : CompleteSpace E := cE
  let : CompleteSpace F := cF
  exact ⟨E, F, gE, gF, nE, nF, cE, cF,
    quotient_parameter_counterexample_of_nowhereAnalytic K E F k
      (hQ (Fin k) (Fintype.card_fin k))⟩

end AlternatingAnalytic
