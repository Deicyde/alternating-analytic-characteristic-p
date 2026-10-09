import AlternatingAnalytic.Analysis.DenseScalarFamilyExtension
import AlternatingAnalytic.Analysis.RigidDenseSourceCoordinates
import AlternatingAnalytic.Analysis.RigidDenseSourceBasic
import AlternatingAnalytic.Analysis.RigidDenseSourceAlgebra

/-!
# Rigidity of the dense source (Lemma H.5)

For `K` dense in a complete `L` and `a` algebraically independent over `K`, every bounded
endomorphism of `E = K^I + K a` is a scalar and every bounded functional `E → K` is zero.
Bounded maps are extended to `L^I`, where they are `L`-linear, and the coefficient comparison
of `RigidDenseSourceAlgebra` applies.
-/

noncomputable section
namespace AlternatingAnalytic.RigidDenseSource
variable {K L I : Type*} [NontriviallyNormedField K] [NontriviallyNormedField L]
  [NormedAlgebra K L] [Fintype I] [CompleteSpace L]
  (S : Submodule K (I → L)) (hd : DenseRange S.subtypeₗᵢ)
  (hKL : DenseRange (algebraMap K L))
/-- The `L`-linear extension of a bounded endomorphism of `S` to `L^I`. -/
def completedEndomorphism (T : S →L[K] S) : (I → L) →L[L] (I → L) :=
  denseScalarLinearExtension hKL
    (denseLinearExtension S.subtypeₗᵢ hd (S.subtypeL.comp T))
@[simp] theorem completedEndomorphism_apply (T : S →L[K] S) (x : S) :
    completedEndomorphism S hd hKL T x = (T x : I → L) := by
  exact denseLinearExtension_apply S.subtypeₗᵢ hd (S.subtypeL.comp T) x

/-- The `L`-linear extension of a bounded functional `S → K` to `L^I → L`. -/
def completedFunctional (f : S →L[K] K) : (I → L) →L[L] L :=
  denseScalarLinearExtension hKL
    (denseLinearExtension S.subtypeₗᵢ hd ((algebraMapCLM K L).comp f))
@[simp] theorem completedFunctional_apply (f : S →L[K] K) (x : S) :
    completedFunctional S hd hKL f x = algebraMap K L (f x) := by
  exact denseLinearExtension_apply S.subtypeₗᵢ hd ((algebraMapCLM K L).comp f) x

section Rigidity

variable [Nonempty I] {a : I → L}

/-- A bounded endomorphism of the dense source is scalar multiplication. -/
theorem exists_scalar (hKL : DenseRange (algebraMap K L))
    (ha : AlgebraicIndependent K a) (T : source K a →L[K] source K a) :
    ∃ s : K, ∀ x, T x = s • x := by
  classical
  let hd := denseRange_subtype (K := K) (a := a) hKL
  let S := completedEndomorphism (source K a) hd hKL T
  have hcolumns (j : I) := (mem_source (K := K) (a := a)).mp (T (standard K a j)).property
  choose M c hcol using hcolumns
  obtain ⟨b, s, hs⟩ := (mem_source (K := K) (a := a)).mp (T (generator K a)).property
  have hS : ∀ x, S x = algebraMap K L s • x := by
    apply ambient_endomorphism_eq_scalar a ha S.toLinearMap (fun i j => M j i) c b s
    · intro i j
      change S (Pi.single j 1) i = _
      rw [← coe_standard K a j]
      dsimp only [S]
      rw [completedEndomorphism_apply]
      exact hcol j i
    · intro i
      change S a i = _
      change S (generator K a : I → L) i = _
      dsimp only [S]
      rw [completedEndomorphism_apply]
      exact hs i
  refine ⟨s, fun x => Subtype.ext ?_⟩
  change (T x : I → L) = s • (x : I → L)
  rw [← completedEndomorphism_apply (source K a) hd hKL T x, hS]
  simp only [algebraMap_smul]

/-- A bounded endomorphism of the source is multiplication by a unique scalar. -/
theorem existsUnique_scalar (hKL : DenseRange (algebraMap K L))
    (ha : AlgebraicIndependent K a) (T : source K a →L[K] source K a) :
    ∃! s : K, ∀ x, T x = s • x := by
  obtain ⟨s, hs⟩ := exists_scalar hKL ha T
  refine ⟨s, hs, fun t ht => ?_⟩
  apply (scalarActionIsometry (K := K) (E := source K a)).injective
  apply ContinuousLinearMap.ext
  intro x
  exact (ht x).symm.trans (hs x)

omit [Nonempty I] in
/-- Every bounded functional from the source to `K` is zero. `K` need not be complete. -/
theorem dual_eq_zero (hKL : DenseRange (algebraMap K L))
    (ha : AlgebraicIndependent K a) (f : source K a →L[K] K) : f = 0 := by
  classical
  let hd := denseRange_subtype (K := K) (a := a) hKL
  let ell := completedFunctional (source K a) hd hKL f
  have hell : ell.toLinearMap = 0 := by
    apply ambient_functional_eq_zero a ha ell.toLinearMap
      (fun j => f (standard K a j)) (f (generator K a))
    · intro j
      change ell (Pi.single j 1) = _
      rw [← coe_standard K a j]
      exact completedFunctional_apply (source K a) hd hKL f (standard K a j)
    · exact completedFunctional_apply (source K a) hd hKL f (generator K a)
  ext x
  apply (algebraMap K L).injective
  change algebraMap K L (f x) = algebraMap K L 0
  rw [map_zero, ← completedFunctional_apply (source K a) hd hKL f x]
  exact LinearMap.congr_fun hell (x : I → L)

/-- The isometry `End(E) ≃ K` sending an endomorphism to its scalar. -/
def endScalarEquiv (hKL : DenseRange (algebraMap K L)) (ha : AlgebraicIndependent K a) :
    (source K a →L[K] source K a) ≃ₗᵢ[K] K :=
  endScalarEquivOfRigidity (exists_scalar hKL ha)

theorem endScalarEquiv_apply (hKL : DenseRange (algebraMap K L))
    (ha : AlgebraicIndependent K a) (T : source K a →L[K] source K a) (x : source K a) :
    T x = endScalarEquiv hKL ha T • x :=
  endScalarEquivOfRigidity_apply (exists_scalar hKL ha) T x

@[simp]
theorem endScalarEquiv_symm_apply (hKL : DenseRange (algebraMap K L))
    (ha : AlgebraicIndependent K a) (s : K) :
    (endScalarEquiv hKL ha).symm s = s • ContinuousLinearMap.id K (source K a) :=
  endScalarEquivOfRigidity_symm_apply (exists_scalar hKL ha) s

@[simp]
theorem norm_endScalarEquiv (hKL : DenseRange (algebraMap K L))
    (ha : AlgebraicIndependent K a) (T : source K a →L[K] source K a) :
    ‖endScalarEquiv hKL ha T‖ = ‖T‖ :=
  (endScalarEquiv hKL ha).norm_map T

omit [CompleteSpace L] in
@[simp]
theorem norm_scalar_id (s : K) :
    ‖s • ContinuousLinearMap.id K (source K a)‖ = ‖s‖ := by
  simpa only [scalarActionIsometry_apply] using
    (scalarActionIsometry (K := K) (E := source K a)).norm_map s

@[simp]
theorem endScalarEquiv_id (hKL : DenseRange (algebraMap K L))
    (ha : AlgebraicIndependent K a) :
    endScalarEquiv hKL ha (ContinuousLinearMap.id K (source K a)) = 1 :=
  endScalarEquivOfRigidity_id (exists_scalar hKL ha)

@[simp]
theorem endScalarEquiv_comp (hKL : DenseRange (algebraMap K L))
    (ha : AlgebraicIndependent K a) (T U : source K a →L[K] source K a) :
    endScalarEquiv hKL ha (T.comp U) = endScalarEquiv hKL ha T * endScalarEquiv hKL ha U :=
  endScalarEquivOfRigidity_comp (exists_scalar hKL ha) T U

end Rigidity
end AlternatingAnalytic.RigidDenseSource
