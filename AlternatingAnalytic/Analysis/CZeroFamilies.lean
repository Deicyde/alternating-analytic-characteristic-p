import AlternatingAnalytic.Analysis.CZeroReflection
import AlternatingAnalytic.Analysis.FiniteCoordinateFamilies
import AlternatingAnalytic.Analysis.SphericalCompleteness

/-!
# Analytic alternating morphism families with discrete c₀ parameters

This file proves `paper/charp.tex`, `fam:cor:c0-families`, including transport
along any supplied continuous linear equivalence of parameter spaces. Only the
final value space must be complete and ultrametric. The scalar field and the
other normed spaces need not be complete; all degrees and discrete index types
are allowed. In fact, the proofs do not need the scalar norm to be ultrametric.

The existing ambient polynomial and isometric inclusion from
`FiniteCoordinateFamilies` reduce the result to `CZeroReflection`. The generic
operator ultrametric instance below supplies the missing strong triangle
inequality, without spherical completeness.
-/

namespace ContinuousLinearMap

variable {K E F : Type*} [NontriviallyNormedField K]
  [SeminormedAddCommGroup E] [NormedSpace K E]
  [SeminormedAddCommGroup F] [NormedSpace K F] [IsUltrametricDist F]

/-- The operator norm inherits the strong triangle inequality from the target. -/
theorem norm_add_le_max_of_ultrametric (f g : E →L[K] F) :
    ‖f + g‖ ≤ max ‖f‖ ‖g‖ := by
  refine (f + g).opNorm_le_bound (le_max_of_le_left (norm_nonneg f)) fun x => ?_
  calc
    ‖(f + g) x‖ = ‖f x + g x‖ := rfl
    _ ≤ max ‖f x‖ ‖g x‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ max ‖f‖ ‖g‖ * ‖x‖ := by
      rw [max_mul_of_nonneg _ _ (norm_nonneg x)]
      exact max_le_max (f.le_opNorm x) (g.le_opNorm x)

/-- Operators into an ultrametric space are ultrametric for the operator norm. -/
instance instIsUltrametricDistOfCodomain : IsUltrametricDist (E →L[K] F) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
    norm_add_le_max_of_ultrametric

end ContinuousLinearMap

open scoped ZeroAtInfty

namespace AlternatingAnalytic

variable {K I E E' F F' P : Type*} [NontriviallyNormedField K]
  [TopologicalSpace I] [DiscreteTopology I]
  [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup E'] [NormedSpace K E']
  [NormedAddCommGroup F] [NormedSpace K F]
  [NormedAddCommGroup F'] [NormedSpace K F'] [CompleteSpace F'] [IsUltrametricDist F']
  [NormedAddCommGroup P] [NormedSpace K P]

/-- Completeness and the strong triangle inequality for the actual alternating
target, action-operator target, and ambient multilinear-operator target. -/
theorem alternatingMapAction_target_properties (k : ℕ) :
    let W := (E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F')
    let Z := (E [⋀^Fin k]→L[K] F) →L[K]
      ContinuousMultilinearMap K (fun _ : Fin k => E') F'
    CompleteSpace (E' [⋀^Fin k]→L[K] F') ∧ IsUltrametricDist (E' [⋀^Fin k]→L[K] F') ∧
      CompleteSpace W ∧ IsUltrametricDist W ∧ CompleteSpace Z ∧ IsUltrametricDist Z := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- Pointwise action analyticity after any bounded linear change of c₀ parameters. -/
theorem analyticAt_alternatingMapAction_comp_of_c0_equiv
    (e : P ≃L[K] C₀(I, K)) (k : ℕ)
    {γ : P → (E' →L[K] E) × (F →L[K] F')} {x : P}
    (hγ : AnalyticAt K γ x) : AnalyticAt K (alternatingMapAction k ∘ γ) x := by
  apply c0_analyticAt_linearIsometry_of_equiv e
    (Z := (E [⋀^Fin k]→L[K] F) →L[K]
      ContinuousMultilinearMap K (fun _ : Fin k => E') F')
    (alternatingMapActionInclusion (K := K) (E := E) (E' := E') (F := F) (F' := F') k)
  exact (analyticAt_ambient_alternatingMapAction k (γ x)).comp hγ

/-- The alternating action of an analytic c₀ family is analytic at that point. -/
theorem analyticAt_alternatingMapAction_comp_of_c0 (k : ℕ)
    {γ : C₀(I, K) → (E' →L[K] E) × (F →L[K] F')} {x : C₀(I, K)}
    (hγ : AnalyticAt K γ x) : AnalyticAt K (alternatingMapAction k ∘ γ) x :=
  analyticAt_alternatingMapAction_comp_of_c0_equiv
    (ContinuousLinearEquiv.refl K C₀(I, K)) k hγ

/-- Analytic families on spaces with supplied c₀ coordinates are admissible on
arbitrary parameter sets. -/
theorem isAdmissibleOn_of_c0_equiv (e : P ≃L[K] C₀(I, K)) (k : ℕ)
    {γ : P → (E' →L[K] E) × (F →L[K] F')} {U : Set P}
    (hγ : AnalyticOnNhd K γ U) : IsAdmissibleOn k γ U :=
  ⟨hγ, fun x hx => analyticAt_alternatingMapAction_comp_of_c0_equiv e k (hγ x hx)⟩

/-- Every analytic c₀ morphism family is admissible on its parameter set. -/
theorem isAdmissibleOn_of_c0 (k : ℕ)
    {γ : C₀(I, K) → (E' →L[K] E) × (F →L[K] F')} {U : Set C₀(I, K)}
    (hγ : AnalyticOnNhd K γ U) : IsAdmissibleOn k γ U :=
  isAdmissibleOn_of_c0_equiv (ContinuousLinearEquiv.refl K C₀(I, K)) k hγ

/-- The open-domain corollary after a bounded linear isomorphism of parameters. -/
theorem isAdmissibleOn_of_c0_equiv_of_isOpen (e : P ≃L[K] C₀(I, K)) (k : ℕ)
    {γ : P → (E' →L[K] E) × (F →L[K] F')} {U : Set P}
    (hU : IsOpen U) (hγ : AnalyticOn K γ U) : IsAdmissibleOn k γ U :=
  isAdmissibleOn_of_c0_equiv e k (hU.analyticOn_iff_analyticOnNhd.mp hγ)

/-- Every analytic morphism family on an open c₀ domain is admissible. -/
theorem isAdmissibleOn_of_c0_of_isOpen (k : ℕ)
    {γ : C₀(I, K) → (E' →L[K] E) × (F →L[K] F')} {U : Set C₀(I, K)}
    (hU : IsOpen U) (hγ : AnalyticOn K γ U) : IsAdmissibleOn k γ U :=
  isAdmissibleOn_of_c0 k (hU.analyticOn_iff_analyticOnNhd.mp hγ)

/-- All conclusions of `fam:cor:c0-families`: the actual target spaces are complete
and ultrametric; the action is analytic pointwise, analytic families are admissible
on arbitrary sets, and the open-domain formulation holds. All analytic conclusions
also hold after any supplied bounded linear isomorphism of parameter spaces.
Only `F'` is assumed complete and ultrametric, with no restriction on degree or
characteristic and no completeness assumption on the field or other fibers. -/
theorem c0_analytic_family_admissibility (k : ℕ) :
    let W := (E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F')
    let Z := (E [⋀^Fin k]→L[K] F) →L[K]
      ContinuousMultilinearMap K (fun _ : Fin k => E') F'
    CompleteSpace (E' [⋀^Fin k]→L[K] F') ∧ IsUltrametricDist (E' [⋀^Fin k]→L[K] F') ∧
    CompleteSpace W ∧ IsUltrametricDist W ∧ CompleteSpace Z ∧ IsUltrametricDist Z ∧
    (∀ (γ : C₀(I, K) → (E' →L[K] E) × (F →L[K] F')) (x : C₀(I, K)),
      AnalyticAt K γ x → AnalyticAt K (alternatingMapAction k ∘ γ) x) ∧
    (∀ (γ : C₀(I, K) → (E' →L[K] E) × (F →L[K] F')) (U : Set C₀(I, K)),
      AnalyticOnNhd K γ U → IsAdmissibleOn k γ U) ∧
    (∀ (γ : C₀(I, K) → (E' →L[K] E) × (F →L[K] F')) (U : Set C₀(I, K)),
      IsOpen U → AnalyticOn K γ U →
        AnalyticOn K (alternatingMapAction k ∘ γ) U ∧ IsAdmissibleOn k γ U) ∧
    (∀ _ : P ≃L[K] C₀(I, K),
      (∀ (γ : P → (E' →L[K] E) × (F →L[K] F')) (x : P),
        AnalyticAt K γ x → AnalyticAt K (alternatingMapAction k ∘ γ) x) ∧
      (∀ (γ : P → (E' →L[K] E) × (F →L[K] F')) (U : Set P),
        AnalyticOnNhd K γ U → IsAdmissibleOn k γ U) ∧
      (∀ (γ : P → (E' →L[K] E) × (F →L[K] F')) (U : Set P),
        IsOpen U → AnalyticOn K γ U →
          AnalyticOn K (alternatingMapAction k ∘ γ) U ∧ IsAdmissibleOn k γ U)) := by
  obtain ⟨hA, hA', hW, hW', hZ, hZ'⟩ := alternatingMapAction_target_properties
    (K := K) (E := E) (E' := E') (F := F) (F' := F') k
  refine ⟨hA, hA', hW, hW', hZ, hZ', ?_, ?_, ?_, ?_⟩
  · exact fun _ _ hγ => analyticAt_alternatingMapAction_comp_of_c0 k hγ
  · exact fun _ _ hγ => isAdmissibleOn_of_c0 k hγ
  · intro γ U hU hγ
    have h := isAdmissibleOn_of_c0_of_isOpen k hU hγ
    exact ⟨h.2.analyticOn, h⟩
  · intro e
    refine ⟨?_, ?_, ?_⟩
    · exact fun _ _ hγ => analyticAt_alternatingMapAction_comp_of_c0_equiv e k hγ
    · exact fun _ _ hγ => isAdmissibleOn_of_c0_equiv e k hγ
    · intro γ U hU hγ
      have h := isAdmissibleOn_of_c0_equiv_of_isOpen e k hU hγ
      exact ⟨h.2.analyticOn, h⟩

end AlternatingAnalytic
