import AlternatingAnalytic.Analysis.DeterminantCoefficientSpaces
import AlternatingAnalytic.Analysis.DeterminantMultiplication
import AlternatingAnalytic.Analysis.DeterminantMultilinearObstruction
import AlternatingAnalytic.Analysis.AnalyticFamilies
import AlternatingAnalytic.Analysis.Homogeneous

/-!
# The nonanalytic determinant coordinate and cross-action

The map `f : E → C`, `f(x) = x_0^p` of equation (H.3), obtained by pulling back the
determinant on `D` along multiplication by `x` and extracting the coefficient. As a map into
`L` it is a polynomial, but as a map into `C` it is not analytic at zero, so the cross-action
from `(D, G)` to `(E, G)` is not analytic. This is the degree-`p` case of Theorem H.4.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators NNReal

namespace AlternatingAnalytic.DeterminantPair

variable (p : ℕ) [Fact p.Prime] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)]
attribute [local instance] preferredNormedFieldK preferredFieldK preferredFieldL

/-- The determinant on `A`, as a `K`-alternating map. -/
def determinantK : (A p r) [⋀^Fin p]→ₗ[K p r] (L p r) where
  __ := (deltaAlternating p r).toMultilinearMap.restrictScalars (K p r)
  map_eq_zero_of_eq' v _i _j hv hij :=
    (deltaAlternating p r).map_eq_zero_of_eq v hv hij

@[simp] theorem determinantK_apply (v : Fin p → A p r) :
    determinantK p r v = delta p r v := deltaAlternating_apply p r v

/-- The determinant as a bounded `G`-valued alternating map on `D`. -/
def determinantD : (D p r) [⋀^Fin p]→L[K p r] (G p r) :=
  (((determinantK p r).compLinearMap (D p r).subtype).codRestrict
    (G p r) (fun x => by
      rw [AlternatingMap.compLinearMap_apply, determinantK_apply]
      exact Submodule.subset_span ⟨x, rfl⟩)).mkContinuous 1
        (fun x => by
          change ‖determinantK p r (fun i => (x i : A p r))‖ ≤ 1 * ∏ i, ‖x i‖
          simpa only [determinantK_apply, one_mul, Submodule.norm_coe] using
            norm_delta_le p r (fun i => (x i : A p r)))

@[simp] theorem determinantD_apply (x : Fin p → D p r) :
    (determinantD p r x : L p r) = delta p r (fun i => (x i : A p r)) :=
  determinantK_apply p r _

@[simp] theorem determinantD_standard :
    (determinantD p r (fun i => ⟨e p r i, e_mem_D p r i⟩) : L p r) = 1 := by
  rw [determinantD_apply, delta_e]

/-- The coordinate `f(x) ∈ C` of equation (H.3): the coefficient of `det ∘ M_x`.
Defining it this way, rather than by the formula `x_0^p`, shows that it lands in `C`. -/
def determinantCoordinate (x : E p r) : C p r :=
  coefficientEquiv p r ((determinantD p r).compContinuousLinearMap (multiplication p r x))

/-- As an element of `L`, `f(x) = x_0^p`. -/
@[simp] theorem determinantCoordinate_scalar (x : E p r) :
    (determinantCoordinate p r x : L p r) =
      TruncatedPolynomial.coeff (L p r) p (x : A p r) 0 ^ p := by
  rw [determinantCoordinate, coefficientEquiv_apply]
  change (determinantD p r (fun i => multiplication p r x
    (RigidDenseSource.Concrete.standard p r i)) : L p r) = _
  rw [determinantD_apply]
  have h (i : Fin p) :
      (multiplication p r x (RigidDenseSource.Concrete.standard p r i) : A p r) =
        (x : A p r) * e p r i := by
    rw [multiplication_apply]
    exact congrArg ((x : A p r) * ·) (subtype_standard p r i)
  simp only [h]
  exact delta_mul_e p r (x : A p r)

/-- `f` is homogeneous of degree `p`. -/
theorem determinantCoordinate_homogeneous (s : K p r) (x : E p r) :
    determinantCoordinate p r (s • x) = s ^ p • determinantCoordinate p r x := by
  apply Subtype.ext
  rw [Submodule.coe_smul_of_tower, determinantCoordinate_scalar, determinantCoordinate_scalar]
  change TruncatedPolynomial.coeff (L p r) p (s • (x : A p r)) 0 ^ p =
    s ^ p • (TruncatedPolynomial.coeff (L p r) p (x : A p r) 0 ^ p)
  rw [← algebraMap_smul (L p r) s (x : A p r), map_smul]
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Algebra.smul_def, map_pow]

@[simp] theorem determinantCoordinate_standard_zero :
    (determinantCoordinate p r (RigidDenseSource.Concrete.standard p r 0) : L p r) = 1 := by
  rw [determinantCoordinate_scalar]
  have h := subtype_standard p r (0 : Fin p)
  change (RigidDenseSource.Concrete.standard p r 0 : A p r) =
    TruncatedPolynomial.basis (L p r) p 0 at h
  rw [h, TruncatedPolynomial.coeff_basis]
  simp

/-- Evaluation at `det` followed by coefficient extraction, as a bounded linear map. -/
def determinantCoordinateEvaluation :
    (((D p r) [⋀^Fin p]→L[K p r] (G p r)) →L[K p r]
      ((E p r) [⋀^Fin p]→L[K p r] (G p r))) →L[K p r] C p r :=
  (coefficientEquiv p r).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (ContinuousLinearMap.apply (K p r) ((E p r) [⋀^Fin p]→L[K p r] (G p r))
      (determinantD p r))

/-- The affine family `x ↦ (M_x, id_G)` of morphisms. -/
def multiplicationSlice (x : E p r) :
    (E p r →L[K p r] D p r) × (G p r →L[K p r] G p r) :=
  (multiplication p r x, ContinuousLinearMap.id (K p r) (G p r))

@[simp] theorem multiplicationSlice_zero :
    multiplicationSlice p r 0 = (0, ContinuousLinearMap.id (K p r) (G p r)) := by
  simp [multiplicationSlice]

theorem analyticAt_multiplicationSlice (x : E p r) :
    AnalyticAt (K p r) (multiplicationSlice p r) x :=
  ((multiplication p r).analyticAt x).prod analyticAt_const

/-- `f` is the cross-action along `x ↦ (M_x, id_G)`, followed by a bounded linear map. -/
theorem determinantCoordinate_eq_action (x : E p r) :
    determinantCoordinate p r x = determinantCoordinateEvaluation p r
      (alternatingMapAction p (multiplicationSlice p r x)) := by
  change coefficientEquiv p r _ = coefficientEquiv p r _
  congr 1

/-- `f : E → C` is not analytic at zero. -/
theorem not_analyticAt_determinantCoordinate :
    ¬ AnalyticAt (K p r) (determinantCoordinate p r) 0 := by
  intro hf
  obtain ⟨B, hB⟩ := AnalyticAt.exists_multilinearMap_eq_of_homogeneous p
    (determinantCoordinate p r) hf (determinantCoordinate_homogeneous p r)
  apply no_multilinear_coordinate p r
  refine ⟨B, ?_⟩
  rw [hB, determinantCoordinate_standard_zero]

/-- The action from `(D, G)` to `(E, G)` is not analytic at `(0, id_G)`. -/
theorem not_analyticAt_crossAction :
    ¬ AnalyticAt (K p r)
      (alternatingMapAction (K := K p r) (E := D p r) (E' := E p r)
        (F := G p r) (F' := G p r) p)
      (0, ContinuousLinearMap.id (K p r) (G p r)) := by
  intro h
  apply not_analyticAt_determinantCoordinate p r
  have hs := h.comp_of_eq (analyticAt_multiplicationSlice p r 0)
    (multiplicationSlice_zero p r)
  have he := ((determinantCoordinateEvaluation p r).analyticAt _).comp hs
  simpa only [Function.comp_def, ← determinantCoordinate_eq_action] using he

/-- The degree-`p` nonanalytic coordinate and cross-action, collected. -/
theorem nonanalytic_determinant_coordinate_and_cross_action :
    (∀ x y : E p r, (x : A p r) * (y : A p r) ∈ D p r) ∧
    (∀ x y : E p r,
      (multiplication p r x y : A p r) = (x : A p r) * (y : A p r)) ∧
    (∀ x : E p r, ‖multiplication p r x‖ ≤ ‖x‖) ∧
    (∀ x y : E p r, completedMultiplication p r (x : A p r) (y : A p r) =
      (multiplication p r x y : A p r)) ∧
    (∀ x : A p r, (multiplicationMatrix p r x).IsLowerTriangular) ∧
    (∀ (x : A p r) (i : Fin p), multiplicationMatrix p r x i i =
      TruncatedPolynomial.coeff (L p r) p x 0) ∧
    (∀ x : A p r, (multiplicationMatrix p r x).det =
      TruncatedPolynomial.coeff (L p r) p x 0 ^ p) ∧
    (∀ v : Fin p → D p r,
      (determinantD p r v : L p r) = delta p r (fun i => (v i : A p r))) ∧
    (determinantD p r (fun i => ⟨e p r i, e_mem_D p r i⟩) : L p r) = 1 ∧
    (∀ x : E p r, determinantCoordinate p r x = coefficientEquiv p r
      ((determinantD p r).compContinuousLinearMap (multiplication p r x))) ∧
    (∀ x : E p r, (determinantCoordinate p r x : L p r) =
      TruncatedPolynomial.coeff (L p r) p (x : A p r) 0 ^ p) ∧
    (∀ (s : K p r) (x : E p r),
      determinantCoordinate p r (s • x) = s ^ p • determinantCoordinate p r x) ∧
    ¬ AnalyticAt (K p r) (determinantCoordinate p r) 0 ∧
    (∀ x : E p r, determinantCoordinate p r x = determinantCoordinateEvaluation p r
      (alternatingMapAction p (multiplicationSlice p r x))) ∧
    (∀ x : E p r, AnalyticAt (K p r) (multiplicationSlice p r) x) ∧
    multiplicationSlice p r 0 = (0, ContinuousLinearMap.id (K p r) (G p r)) ∧
    ¬ AnalyticAt (K p r)
      (alternatingMapAction (K := K p r) (E := D p r) (E' := E p r)
        (F := G p r) (F' := G p r) p)
      (0, ContinuousLinearMap.id (K p r) (G p r)) := by
  exact ⟨mul_mem_D p r, multiplication_apply p r, norm_multiplication_apply_le p r,
    completedMultiplication_apply_source p r, multiplicationMatrix_isLowerTriangular p r,
    multiplicationMatrix_diag p r, det_multiplicationMatrix p r, determinantD_apply p r,
    determinantD_standard p r, fun _ => rfl, determinantCoordinate_scalar p r,
    determinantCoordinate_homogeneous p r, not_analyticAt_determinantCoordinate p r,
    determinantCoordinate_eq_action p r, analyticAt_multiplicationSlice p r,
    multiplicationSlice_zero p r, not_analyticAt_crossAction p r⟩

end AlternatingAnalytic.DeterminantPair
