import AlternatingAnalytic.Main
import AlternatingAnalytic.Analysis.L1BanachQuotient
import AlternatingAnalytic.Analysis.L1Families
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# Failure of descent through ordinary ℓ¹ quotient parameters

The actual closed-unit-ball quotient makes alternating precomposition analytic upstairs,
while the Banach counterexample from `Main` remains nowhere analytic downstairs.
A section differentiable at even one point would split the quotient by its derivative.
Separately, analyticity along every bounded map out of ordinary ℓ¹ rules out every
bounded linear ℓ¹ retract, with an index universe independent of the field universe.

A total map `s : H → ℓ¹` with the section equation on an open `U` encodes a section
on `U` (extend it by zero outside `U`). At a point of `U`, differentiability depends
only on this restriction. The conclusions concern differentiable sections.
The original ordinary operator norm on `H` and sum norm on `lp` are retained.
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

/-- If an analytic pullback has a nonanalytic value downstairs, no local section is
differentiable even at its base point. -/
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

/-- Total maps encode sections on an open domain: values outside the domain do not
affect differentiability at a point of the domain. -/
theorem not_differentiableAt_section_of_isOpen
    (q : X →L[K] H) {f : H → Y}
    (hf : AnalyticOnNhd K (f ∘ q) Set.univ)
    {h : H} (hnot : ¬AnalyticAt K f h)
    {U : Set H} (hU : IsOpen U) {s : H → X}
    (hsection : ∀ h ∈ U, q (s h) = h) {h₀ : H} (hh₀ : h₀ ∈ U) :
    ¬DifferentiableAt K s h₀ := by
  apply not_differentiableAt_of_local_section q hf hnot
  exact Filter.eventually_of_mem (hU.mem_nhds hh₀) hsection

/-- The corresponding relative differentiability statement on the open domain. -/
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

/-- The action of a morphism with identity second component is actual alternating
precomposition. -/
@[simp]
theorem alternatingMapAction_pair_id_eq_Q (k : ℕ) (u : E →L[K] E) :
    alternatingMapAction k (u, ContinuousLinearMap.id K F) =
      Round24Transfer.Q K (Fin k) E E F u := by
  ext m x
  rfl

/-- Every bounded map from arbitrary ordinary ℓ¹ parameters gives an admissible
precomposition family. The index universe is independent of all space universes. -/
theorem isAdmissibleOn_l1_precomposition [CompleteSpace F] (k : ℕ) {I : Type v}
    (r : L1 K I →L[K] (E →L[K] E)) :
    IsAdmissibleOn k (fun a => (r a, ContinuousLinearMap.id K F)) Set.univ := by
  exact isAdmissibleOn_of_l1 k ((r.analyticOnNhd Set.univ).prod analyticOnNhd_const)

/-- Alternating precomposition is analytic after every bounded map from ordinary
ℓ¹, on the whole parameter space. -/
theorem analyticOnNhd_Q_comp_l1 [CompleteSpace F] (k : ℕ) {I : Type v}
    (r : L1 K I →L[K] (E →L[K] E)) :
    AnalyticOnNhd K (Round24Transfer.Q K (Fin k) E E F ∘ r) Set.univ := by
  simpa only [Function.comp_def, alternatingMapAction_pair_id_eq_Q] using
    (isAdmissibleOn_l1_precomposition (F := F) k r).2

/-- A nowhere analytic alternating-precomposition map rules out every bounded
linear retract through ordinary ℓ¹, with arbitrary independent index universe. -/
theorem no_l1_retract_of_nowhere_analytic_Q [CompleteSpace F] (k : ℕ)
    (hQ : ∀ h : E →L[K] E, ¬AnalyticAt K (Round24Transfer.Q K (Fin k) E E F) h)
    (I : Type v) (i : (E →L[K] E) →L[K] L1 K I)
    (r : L1 K I →L[K] (E →L[K] E)) :
    r.comp i ≠ ContinuousLinearMap.id K (E →L[K] E) := by
  intro hri
  have hri_apply (h : E →L[K] E) : r (i h) = h := DFunLike.congr_fun hri h
  have hcomp : (Round24Transfer.Q K (Fin k) E E F ∘ r) ∘ i =
      Round24Transfer.Q K (Fin k) E E F := by
    funext h
    exact congrArg (Round24Transfer.Q K (Fin k) E E F) (hri_apply h)
  have h := ((analyticOnNhd_Q_comp_l1 (F := F) k r) (i 0) (Set.mem_univ _)).comp
    (i.analyticAt 0)
  rw [hcomp] at h
  exact hQ 0 h


end L1Precomposition

section Counterexample

variable (K E F : Type*) [NontriviallyNormedField K]
  [NormedAddCommGroup E] [NormedSpace K E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace K F] [CompleteSpace F]

/-- For fixed Banach counterexample spaces, the actual unit-ball quotient has analytic
pullback, no local section differentiable at any point, and no bounded ℓ¹ retract
through any index type in the independent universe `v`. -/
theorem quotient_parameter_counterexample_of_nowhereAnalytic (k : ℕ)
    (hQ : ∀ h : E →L[K] E, ¬AnalyticAt K (Round24Transfer.Q K (Fin k) E E F) h) :
    let H := E →L[K] E
    let J := L1UnitBallIndex H
    let q := unitBallL1Quotient K H
    let Q := Round24Transfer.Q K (Fin k) E E F
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

/-- Failure of descent through quotient parameters and the all-ℓ¹ non-retract consequence
of `fam:cor:quotient-parameters`, for the same Banach spaces and the actual unit-ball
quotient. Positive characteristic supplies primality; no additional norm hypotheses
are imposed on the spaces. The arbitrary ℓ¹ index lives in the independent universe `v`. -/
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
          let Q := Round24Transfer.Q K (Fin k) E E F
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
