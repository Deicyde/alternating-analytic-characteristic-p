import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Field.Instances

/-!
# Restriction along a dense scalar inclusion

Continuous linear, multilinear, and alternating maps over a dense normed
subfield are automatically maps over the larger field, with the same underlying
functions and norms. This is the map-identification part of the paper's descent
lemma. No completeness assumption on the input or output spaces is used.
-/

namespace AlternatingAnalytic

section DenseScalars

variable {K L E F : Type*} [NontriviallyNormedField K] [NontriviallyNormedField L]
  [NormedAlgebra K L]
  [NormedAddCommGroup E] [NormedSpace K E] [NormedSpace L E] [IsScalarTower K L E]
  [NormedAddCommGroup F] [NormedSpace K F] [NormedSpace L F] [IsScalarTower K L F]

/-- Continuity promotes original-field linearity to extension-field linearity
when the scalar inclusion has dense range. -/
theorem map_smul_of_dense_algebraMap (hd : DenseRange (algebraMap K L))
    (f : E →L[K] F) (c : L) (x : E) : f (c • x) = c • f x := by
  have h : (fun a : L => f (a • x)) = fun a : L => a • f x := by
    apply hd.equalizer (f.continuous.comp (continuous_id.smul continuous_const))
      (continuous_id.smul continuous_const)
    funext a
    change f ((algebraMap K L a) • x) = (algebraMap K L a) • f x
    simpa only [algebraMap_smul] using f.map_smul a x
  exact congrFun h c

/-- A continuous map over the smaller field, with its proved larger-field
linear structure and unchanged underlying function. -/
def denseScalarLinearExtension (hd : DenseRange (algebraMap K L))
    (f : E →L[K] F) : E →L[L] F where
  toFun := f
  map_add' := f.map_add
  map_smul' := map_smul_of_dense_algebraMap hd f
  cont := f.continuous

@[simp]
theorem denseScalarLinearExtension_apply (hd : DenseRange (algebraMap K L))
    (f : E →L[K] F) (x : E) : denseScalarLinearExtension hd f x = f x := rfl

@[simp]
theorem restrict_denseScalarLinearExtension (hd : DenseRange (algebraMap K L))
    (f : E →L[K] F) : (denseScalarLinearExtension hd f).restrictScalars K = f := by
  ext x
  rfl

@[simp]
theorem norm_denseScalarLinearExtension (hd : DenseRange (algebraMap K L))
    (f : E →L[K] F) : ‖denseScalarLinearExtension hd f‖ = ‖f‖ := by
  rw [← ContinuousLinearMap.norm_restrictScalars (𝕜' := K),
    restrict_denseScalarLinearExtension]

/-- The actual spaces of continuous linear maps are linearly isometric over
the larger field; the inverse is restriction of scalars. -/
def denseScalarLinearEquiv (hd : DenseRange (algebraMap K L)) :
    (E →L[K] F) ≃ₗᵢ[L] (E →L[L] F) where
  toFun := denseScalarLinearExtension hd
  invFun := ContinuousLinearMap.restrictScalars K
  left_inv := restrict_denseScalarLinearExtension hd
  right_inv f := by ext x; rfl
  map_add' f g := by ext x; rfl
  map_smul' c f := by ext x; rfl
  norm_map' := norm_denseScalarLinearExtension hd

@[simp]
theorem denseScalarLinearEquiv_apply (hd : DenseRange (algebraMap K L))
    (f : E →L[K] F) (x : E) : denseScalarLinearEquiv hd f x = f x := rfl

@[simp]
theorem denseScalarLinearEquiv_symm_apply (hd : DenseRange (algebraMap K L))
    (f : E →L[L] F) : (denseScalarLinearEquiv hd).symm f = f.restrictScalars K := rfl

variable {n : ℕ}

/-- Every scalar identity in every slot follows from the dense scalar
inclusion, applied to the continuous linear map in that slot. -/
def denseScalarMultilinearExtension (hd : DenseRange (algebraMap K L))
    (f : E [×n]→L[K] F) : E [×n]→L[L] F where
  toFun := f
  map_update_add' := f.map_update_add
  map_update_smul' x i c y := map_smul_of_dense_algebraMap hd (f.toContinuousLinearMap x i) c y
  cont := f.cont

@[simp]
theorem denseScalarMultilinearExtension_apply (hd : DenseRange (algebraMap K L))
    (f : E [×n]→L[K] F) (x : Fin n → E) : denseScalarMultilinearExtension hd f x = f x := rfl

@[simp]
theorem restrict_denseScalarMultilinearExtension (hd : DenseRange (algebraMap K L))
    (f : E [×n]→L[K] F) : (denseScalarMultilinearExtension hd f).restrictScalars K = f := by
  ext x
  rfl

@[simp]
theorem norm_denseScalarMultilinearExtension (hd : DenseRange (algebraMap K L))
    (f : E [×n]→L[K] F) : ‖denseScalarMultilinearExtension hd f‖ = ‖f‖ := rfl

/-- Isometric identification of continuous multilinear map spaces, with
inverse given by actual scalar restriction. -/
def denseScalarMultilinearEquiv (hd : DenseRange (algebraMap K L)) :
    (E [×n]→L[K] F) ≃ₗᵢ[L] (E [×n]→L[L] F) where
  toFun := denseScalarMultilinearExtension hd
  invFun := ContinuousMultilinearMap.restrictScalars K
  left_inv := restrict_denseScalarMultilinearExtension hd
  right_inv f := by ext x; rfl
  map_add' f g := by ext x; rfl
  map_smul' c f := by ext x; rfl
  norm_map' := norm_denseScalarMultilinearExtension hd

@[simp]
theorem denseScalarMultilinearEquiv_apply (hd : DenseRange (algebraMap K L))
    (f : E [×n]→L[K] F) (x : Fin n → E) :
    denseScalarMultilinearEquiv (E := E) (F := F) (n := n) hd f x = f x := rfl

@[simp]
theorem denseScalarMultilinearEquiv_symm_apply (hd : DenseRange (algebraMap K L))
    (f : E [×n]→L[L] F) :
    (denseScalarMultilinearEquiv (E := E) (F := F) (n := n) hd).symm f =
      f.restrictScalars K := rfl

/-- Alternation is preserved because the underlying multilinear function is
unchanged, including its equal-input vanishing property. -/
def denseScalarAlternatingExtension (hd : DenseRange (algebraMap K L))
    (f : E [⋀^Fin n]→L[K] F) : E [⋀^Fin n]→L[L] F :=
  ⟨denseScalarMultilinearExtension hd f.toContinuousMultilinearMap,
    fun x _ _ h hij => f.map_eq_zero_of_eq x h hij⟩

@[simp]
theorem denseScalarAlternatingExtension_apply (hd : DenseRange (algebraMap K L))
    (f : E [⋀^Fin n]→L[K] F) (x : Fin n → E) : denseScalarAlternatingExtension hd f x = f x := rfl

@[simp]
theorem restrict_denseScalarAlternatingExtension (hd : DenseRange (algebraMap K L))
    (f : E [⋀^Fin n]→L[K] F) : (denseScalarAlternatingExtension hd f).restrictScalars K = f := by
  ext x
  rfl

@[simp]
theorem norm_denseScalarAlternatingExtension (hd : DenseRange (algebraMap K L))
    (f : E [⋀^Fin n]→L[K] F) : ‖denseScalarAlternatingExtension hd f‖ = ‖f‖ := rfl

/-- Isometric identification of continuous alternating map spaces over a
dense field inclusion, linear over the larger field. -/
def denseScalarAlternatingEquiv (hd : DenseRange (algebraMap K L)) :
    (E [⋀^Fin n]→L[K] F) ≃ₗᵢ[L] (E [⋀^Fin n]→L[L] F) where
  toFun := denseScalarAlternatingExtension hd
  invFun := ContinuousAlternatingMap.restrictScalars K
  left_inv := restrict_denseScalarAlternatingExtension hd
  right_inv f := by ext x; rfl
  map_add' f g := by ext x; rfl
  map_smul' c f := by ext x; rfl
  norm_map' := norm_denseScalarAlternatingExtension hd

@[simp]
theorem denseScalarAlternatingEquiv_apply (hd : DenseRange (algebraMap K L))
    (f : E [⋀^Fin n]→L[K] F) (x : Fin n → E) : denseScalarAlternatingEquiv hd f x = f x := rfl

@[simp]
theorem denseScalarAlternatingEquiv_symm_apply (hd : DenseRange (algebraMap K L))
    (f : E [⋀^Fin n]→L[L] F) : (denseScalarAlternatingEquiv hd).symm f = f.restrictScalars K := rfl

end DenseScalars

section Completion

variable (K : Type*) [NontriviallyNormedField K]

/-- The field completion retains a scalar of norm greater than one. -/
noncomputable instance completionNontriviallyNormedField :
    NontriviallyNormedField (UniformSpace.Completion K) where
  __ : NormedField (UniformSpace.Completion K) := inferInstance
  non_trivial := by
    obtain ⟨x, hx⟩ := NormedField.exists_one_lt_norm K
    exact ⟨(x : UniformSpace.Completion K), by simpa using hx⟩

/-- The algebra map to the actual field completion has dense range. -/
theorem denseRange_algebraMap_completion :
    DenseRange (algebraMap K (UniformSpace.Completion K)) := by
  change DenseRange (fun x : K => (x : UniformSpace.Completion K))
  exact UniformSpace.Completion.denseRange_coe

/-- The same algebra map is isometric. -/
theorem isometry_algebraMap_completion :
    Isometry (algebraMap K (UniformSpace.Completion K)) :=
  algebraMap_isometry K (UniformSpace.Completion K)

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace K E] [NormedSpace (UniformSpace.Completion K) E]
  [IsScalarTower K (UniformSpace.Completion K) E]
  [NormedAddCommGroup F] [NormedSpace K F] [NormedSpace (UniformSpace.Completion K) F]
  [IsScalarTower K (UniformSpace.Completion K) F]

/-- Completion specialization of the linear map identification. -/
noncomputable def completionScalarLinearEquiv :
    (E →L[K] F) ≃ₗᵢ[UniformSpace.Completion K] (E →L[UniformSpace.Completion K] F) :=
  denseScalarLinearEquiv (denseRange_algebraMap_completion K)

/-- Completion specialization of the multilinear map identification. -/
noncomputable def completionScalarMultilinearEquiv (n : ℕ) :
    (E [×n]→L[K] F) ≃ₗᵢ[UniformSpace.Completion K] (E [×n]→L[UniformSpace.Completion K] F) :=
  denseScalarMultilinearEquiv (denseRange_algebraMap_completion K)

/-- Completion specialization of the alternating map identification. -/
noncomputable def completionScalarAlternatingEquiv (n : ℕ) :
    (E [⋀^Fin n]→L[K] F) ≃ₗᵢ[UniformSpace.Completion K]
      (E [⋀^Fin n]→L[UniformSpace.Completion K] F) :=
  denseScalarAlternatingEquiv (denseRange_algebraMap_completion K)

end Completion

end AlternatingAnalytic
