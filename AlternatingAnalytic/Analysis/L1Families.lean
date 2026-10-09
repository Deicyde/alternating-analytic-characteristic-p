import AlternatingAnalytic.Analysis.FiniteCoordinateFamilies
import AlternatingAnalytic.Analysis.L1FixedDegreeReflection

/-!
# Alternating families over ℓ¹ parameters and their retracts

Analytic morphism families parametrized by an open subset of ℓ¹(I, K), or of a bounded
linear retract of it, are admissible: the joint alternating action along them is analytic.
This is Theorem 4.5(2) applied to the degree `k + 1` ambient representative of the joint
action, and gives the ℓ¹ row of Corollary 4.6. Only the final value space `F'` is assumed
complete.
-/

open L1Coordinates (L1)

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace AlternatingAnalytic

variable {K I E E' F F' P : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup E'] [NormedSpace K E']
  [NormedAddCommGroup F] [NormedSpace K F]
  [NormedAddCommGroup F'] [NormedSpace K F'] [CompleteSpace F']
  [NormedAddCommGroup P] [NormedSpace K P]

/-- The joint action is analytic along an analytic family on ℓ¹. -/
theorem analyticAt_alternatingMapAction_comp_of_l1 (k : ℕ)
    {γ : L1 K I → (E' →L[K] E) × (F →L[K] F')} {x : L1 K I}
    (hγ : AnalyticAt K γ x) : AnalyticAt K (alternatingMapAction k ∘ γ) x := by
  let : CompleteSpace (ContinuousMultilinearMap K (fun _ : Fin k => E') F') :=
    inferInstance
  let : CompleteSpace ((E [⋀^Fin k]→L[K] F) →L[K]
      ContinuousMultilinearMap K (fun _ : Fin k => E') F') := inferInstance
  refine analyticAt_comp_of_l1_fixed_degree_isometry
    (K := K) (I := I)
    (H := (E' →L[K] E) × (F →L[K] F'))
    (Z := (E [⋀^Fin k]→L[K] F) →L[K]
      ContinuousMultilinearMap K (fun _ : Fin k => E') F')
    (V := (E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F'))
    (alternatingMapActionInclusion (K := K) (E := E) (E' := E') (F := F) (F' := F') k)
    (isClosed_range_alternatingMapActionInclusion
      (K := K) (E := E) (E' := E') (F := F) (F' := F') k) (k + 1)
    (ambientAlternatingMapAction (K := K) (E := E) (E' := E') (F := F) (F' := F') k)
    (alternatingMapAction (K := K) (E := E) (E' := E') (F := F) (F' := F') k) ?_ hγ
  intro h
  exact (ambientAlternatingMapAction_diag
    (K := K) (E := E) (E' := E') (F := F) (F' := F') k h).symm

/-- Every analytic morphism family on a subset of ℓ¹ is admissible. -/
theorem isAdmissibleOn_of_l1 (k : ℕ)
    {γ : L1 K I → (E' →L[K] E) × (F →L[K] F')} {U : Set (L1 K I)}
    (hγ : AnalyticOnNhd K γ U) : IsAdmissibleOn k γ U :=
  ⟨hγ, fun x hx => analyticAt_alternatingMapAction_comp_of_l1 k (hγ x hx)⟩

/-- Open-domain version of `isAdmissibleOn_of_l1`. -/
theorem isAdmissibleOn_of_l1_of_isOpen (k : ℕ)
    {γ : L1 K I → (E' →L[K] E) × (F →L[K] F')} {U : Set (L1 K I)}
    (hU : IsOpen U) (hγ : AnalyticOn K γ U) : IsAdmissibleOn k γ U :=
  isAdmissibleOn_of_l1 k (hU.analyticOn_iff_analyticOnNhd.mp hγ)

/-- Every analytic morphism family on a bounded linear retract `P` of ℓ¹ is admissible.
`P` need not be complete. -/
theorem isAdmissibleOn_of_l1_retract (k : ℕ)
    (i : P →L[K] L1 K I) (r : L1 K I →L[K] P)
    (hri : r.comp i = ContinuousLinearMap.id K P)
    {γ : P → (E' →L[K] E) × (F →L[K] F')} {U : Set P}
    (hγ : AnalyticOnNhd K γ U) : IsAdmissibleOn k γ U := by
  have hri_apply (x : P) : r (i x) = x :=
    DFunLike.congr_fun hri x
  have hpull : IsAdmissibleOn k (γ ∘ r) (r ⁻¹' U) :=
    isAdmissibleOn_of_l1 k (hγ.comp (r.analyticOnNhd _) (fun _ hx => hx))
  have hmaps : Set.MapsTo i U (r ⁻¹' U) := by
    intro x hx
    change r (i x) ∈ U
    rwa [hri_apply]
  have hcomp : (γ ∘ r) ∘ i = γ := by
    funext x
    exact congrArg γ (hri_apply x)
  simpa only [hcomp] using hpull.reparam (i.analyticOnNhd U) hmaps

/-- The joint action is analytic at every analytic point of a family on a bounded
linear retract of ℓ¹. -/
theorem analyticAt_alternatingMapAction_comp_of_l1_retract (k : ℕ)
    (i : P →L[K] L1 K I) (r : L1 K I →L[K] P)
    (hri : r.comp i = ContinuousLinearMap.id K P)
    {γ : P → (E' →L[K] E) × (F →L[K] F')} {x : P}
    (hγ : AnalyticAt K γ x) : AnalyticAt K (alternatingMapAction k ∘ γ) x := by
  have hsingleton : AnalyticOnNhd K γ {x} := by
    intro y hy
    simpa only [Set.mem_singleton_iff.mp hy] using hγ
  exact (isAdmissibleOn_of_l1_retract k i r hri hsingleton).2 x (Set.mem_singleton x)

/-- Open-domain version of `isAdmissibleOn_of_l1_retract`. -/
theorem isAdmissibleOn_of_l1_retract_of_isOpen (k : ℕ)
    (i : P →L[K] L1 K I) (r : L1 K I →L[K] P)
    (hri : r.comp i = ContinuousLinearMap.id K P)
    {γ : P → (E' →L[K] E) × (F →L[K] F')} {U : Set P}
    (hU : IsOpen U) (hγ : AnalyticOn K γ U) : IsAdmissibleOn k γ U :=
  isAdmissibleOn_of_l1_retract k i r hri (hU.analyticOn_iff_analyticOnNhd.mp hγ)

/-- Analytic morphism families on ℓ¹, and on any bounded linear retract of ℓ¹, are
admissible. -/
theorem l1_family_admissibility (k : ℕ) :
    (∀ (γ : L1 K I → (E' →L[K] E) × (F →L[K] F')) (U : Set (L1 K I)),
      AnalyticOnNhd K γ U → IsAdmissibleOn k γ U) ∧
    (∀ (i : P →L[K] L1 K I) (r : L1 K I →L[K] P),
      r.comp i = ContinuousLinearMap.id K P →
      ∀ (γ : P → (E' →L[K] E) × (F →L[K] F')) (U : Set P),
        AnalyticOnNhd K γ U → IsAdmissibleOn k γ U) :=
  ⟨fun _ _ hγ => isAdmissibleOn_of_l1 k hγ,
    fun i r hri _ _ hγ => isAdmissibleOn_of_l1_retract k i r hri hγ⟩

end AlternatingAnalytic
