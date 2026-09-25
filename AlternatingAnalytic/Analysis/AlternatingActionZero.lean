import AlternatingAnalytic.Analysis.AnalyticFamilies

/-!
# Degree-zero alternating-map action

The canonical isometry `constOfIsEmptyLIE` identifies a degree-zero alternating
map with its constant value. Under this identification, the joint action is
exactly the covariant continuous linear map; the contravariant map has no effect.
-/

noncomputable section

namespace AlternatingAnalytic

variable {K : Type*} [NontriviallyNormedField K]
  {E E' F F' : Type*}
  [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup E'] [NormedSpace K E']
  [NormedAddCommGroup F] [NormedSpace K F]
  [NormedAddCommGroup F'] [NormedSpace K F']

/-- In degree zero, the action sends the constant with value `y` to the
constant with value `v y`. -/
@[simp]
theorem alternatingMapAction_zero_const (u : E' →L[K] E) (v : F →L[K] F') (y : F) :
    alternatingMapAction 0 (u, v)
        (ContinuousAlternatingMap.constOfIsEmptyLIE K E F (Fin 0) y) =
      ContinuousAlternatingMap.constOfIsEmptyLIE K E' F' (Fin 0) (v y) := by
  ext x
  rfl

/-- Evaluating after the zero-degree identification gives exactly `v`. -/
@[simp]
theorem alternatingMapAction_zero_conjugate_apply
    (u : E' →L[K] E) (v : F →L[K] F') (y : F) :
    (ContinuousAlternatingMap.constOfIsEmptyLIE K E' F' (Fin 0)).symm
        (alternatingMapAction 0 (u, v)
          (ContinuousAlternatingMap.constOfIsEmptyLIE K E F (Fin 0) y)) = v y := by
  rw [alternatingMapAction_zero_const]
  exact (ContinuousAlternatingMap.constOfIsEmptyLIE K E' F' (Fin 0)).symm_apply_apply _

/-- The zero-degree action, conjugated by the canonical linear isometries, is
the covariant map as an equality of continuous linear maps. -/
theorem alternatingMapAction_zero_conjugate (u : E' →L[K] E) (v : F →L[K] F') :
    ((ContinuousAlternatingMap.constOfIsEmptyLIE K E' F' (Fin 0)).symm :
      (E' [⋀^Fin 0]→L[K] F') →L[K] F').comp
        ((alternatingMapAction 0 (u, v)).comp
          (ContinuousAlternatingMap.constOfIsEmptyLIE K E F (Fin 0) :
            F →L[K] (E [⋀^Fin 0]→L[K] F))) =
      v := by
  ext y
  exact alternatingMapAction_zero_conjugate_apply u v y

/-- An explicit formula for the zero-degree action in the original alternating
map spaces. -/
theorem alternatingMapAction_zero_eq (u : E' →L[K] E) (v : F →L[K] F') :
    alternatingMapAction 0 (u, v) =
      (ContinuousAlternatingMap.constOfIsEmptyLIE K E' F' (Fin 0) :
        F' →L[K] (E' [⋀^Fin 0]→L[K] F')).comp
        (v.comp
          ((ContinuousAlternatingMap.constOfIsEmptyLIE K E F (Fin 0)).symm :
            (E [⋀^Fin 0]→L[K] F) →L[K] F)) := by
  ext m x
  change v (m (fun i => u (x i))) = v (m 0)
  exact congrArg (fun z => v (m z)) (Subsingleton.elim _ _)

/-- The contravariant morphism has no effect in degree zero. -/
theorem alternatingMapAction_zero_independent (u₁ u₂ : E' →L[K] E) (v : F →L[K] F') :
    alternatingMapAction 0 (u₁, v) = alternatingMapAction 0 (u₂, v) := by
  rw [alternatingMapAction_zero_eq u₁ v, alternatingMapAction_zero_eq u₂ v]

/-- The zero-degree action has exactly the operator norm of the covariant map. -/
@[simp]
theorem norm_alternatingMapAction_zero (u : E' →L[K] E) (v : F →L[K] F') :
    ‖alternatingMapAction 0 (u, v)‖ = ‖v‖ := by
  rw [alternatingMapAction_zero_eq]
  exact (ContinuousLinearMap.opNorm_linearIsometryEquiv_comp _ _).trans
    (ContinuousLinearMap.opNorm_comp_linearIsometryEquiv _ _)

/-- The degree-zero identification, its action formula and independence from
the contravariant map, together with the exact norm, collected in one public theorem. -/
theorem alternatingMapAction_zero (u : E' →L[K] E) (v : F →L[K] F') :
    (∀ y : F, alternatingMapAction 0 (u, v)
        (ContinuousAlternatingMap.constOfIsEmptyLIE K E F (Fin 0) y) =
      ContinuousAlternatingMap.constOfIsEmptyLIE K E' F' (Fin 0) (v y)) ∧
    ((ContinuousAlternatingMap.constOfIsEmptyLIE K E' F' (Fin 0)).symm :
      (E' [⋀^Fin 0]→L[K] F') →L[K] F').comp
        ((alternatingMapAction 0 (u, v)).comp
          (ContinuousAlternatingMap.constOfIsEmptyLIE K E F (Fin 0) :
            F →L[K] (E [⋀^Fin 0]→L[K] F))) = v ∧
    (∀ u' : E' →L[K] E, alternatingMapAction 0 (u, v) = alternatingMapAction 0 (u', v)) ∧
    ‖alternatingMapAction 0 (u, v)‖ = ‖v‖ :=
  ⟨alternatingMapAction_zero_const u v, alternatingMapAction_zero_conjugate u v,
    (fun u' => alternatingMapAction_zero_independent u u' v),
    norm_alternatingMapAction_zero u v⟩

end AlternatingAnalytic
