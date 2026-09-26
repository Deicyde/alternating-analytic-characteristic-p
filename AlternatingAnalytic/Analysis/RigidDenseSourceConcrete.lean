import AlternatingAnalytic.Analysis.RigidDenseSourceGeneric
import AlternatingAnalytic.Analysis.RationalLaurentScalars
import AlternatingAnalytic.Analysis.TruncatedPolynomialMaxNorm

/-! The literal rigid source in the maximum-norm truncated polynomial algebra. -/
noncomputable section
open scoped BigOperators NNReal
namespace AlternatingAnalytic.RigidDenseSource.Concrete

variable (p : ℕ) [Fact p.Prime] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)]

abbrev K := RationalField (ZMod p) r
abbrev L := LaurentField (ZMod p) r
local instance preferredNormedFieldK : NormedField (K p r) :=
  (inferInstance : NontriviallyNormedField (K p r)).toNormedField
local instance preferredFieldK : Field (K p r) :=
  (inferInstance : NontriviallyNormedField (K p r)).toField
local instance preferredFieldL : Field (L p r) :=
  (inferInstance : NontriviallyNormedField (L p r)).toField

abbrev A := TruncatedPolynomial.A (L p r) p

instance instNormedAddCommGroup : NormedAddCommGroup (A p r) :=
  TruncatedPolynomial.instNormedAddCommGroup (L p r) p
instance instNormedSpaceL : NormedSpace (L p r) (A p r) :=
  TruncatedPolynomial.instNormedSpace (L p r) p
instance instNormedSpaceK : NormedSpace (K p r) (A p r) :=
  { (inferInstance : Module (K p r) (A p r)) with
    norm_smul_le := fun c x => by
      rw [← algebraMap_smul (L p r) c x]
      exact (norm_smul_le (algebraMap (K p r) (L p r) c) x).trans_eq
        (by rw [norm_algebraMap']) }
instance instCompleteSpace : CompleteSpace (A p r) :=
  TruncatedPolynomial.instCompleteSpace (L p r) p

/-- The primary coordinates and all auxiliary scalars come from one independent family. -/
def a : Fin p → L p r :=
  RationalLaurentScalars.a p r (RationalLaurentScalars.AuxiliaryIndex p)

/-- The actual coefficient isometry, restricted to the rational scalar field. -/
def coordinates : A p r ≃ₗᵢ[K p r] (Fin p → L p r) :=
  { (TruncatedPolynomial.coefficientIsometry (L p r) p).toEquiv with
    map_add' := (TruncatedPolynomial.coefficientIsometry (L p r) p).map_add
    map_smul' := fun c x => by
      change TruncatedPolynomial.coefficientIsometry (L p r) p (c • x) = _
      rw [← algebraMap_smul (L p r) c x, map_smul]
      exact algebraMap_smul (L p r) c _
    norm_map' := (TruncatedPolynomial.coefficientIsometry (L p r) p).norm_map }

theorem coordinates_apply (x : A p r) :
    coordinates p r x = TruncatedPolynomial.coefficientIsometry (L p r) p x := rfl

/-- The vector called `a` in the manuscript's truncated algebra. -/
def vector : A p r := (coordinates p r).symm (a p r)

theorem vector_expansion : vector p r =
    ∑ i : Fin p, a p r i • TruncatedPolynomial.epsilon (L p r) p ^ (i : ℕ) :=
  TruncatedPolynomial.coefficientIsometry_symm_apply (L p r) p (a p r)

/-- The literal source in `A`, carrying its inherited maximum norm. -/
def source : Submodule (K p r) (A p r) :=
  (RigidDenseSource.source (K p r) (a p r)).comap (coordinates p r).toLinearMap

/-- Exact coefficient coordinates identify the two actual subspaces. -/
def sourceEquiv : source p r ≃ₗᵢ[K p r] RigidDenseSource.source (K p r) (a p r) where
  toFun x := ⟨coordinates p r x, x.property⟩
  invFun y := ⟨(coordinates p r).symm y, by
    change coordinates p r ((coordinates p r).symm y) ∈ RigidDenseSource.source (K p r) (a p r)
    simp only [LinearIsometryEquiv.apply_symm_apply]; exact y.property⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp
  norm_map' x := (coordinates p r).norm_map x

@[simp] theorem sourceEquiv_apply (x : source p r) :
    (sourceEquiv p r x : Fin p → L p r) = coordinates p r x := rfl

@[simp] theorem sourceEquiv_symm_apply
    (x : RigidDenseSource.source (K p r) (a p r)) :
    ((sourceEquiv p r).symm x : A p r) = (coordinates p r).symm x := rfl

theorem algebraicIndependent_a : AlgebraicIndependent (K p r) (a p r) :=
  RationalLaurentScalars.algebraicIndependent_a p r (RationalLaurentScalars.AuxiliaryIndex p)

theorem mem_source_coordinates (x : A p r) : x ∈ source p r ↔
    ∃ b : Fin p → K p r, ∃ s : K p r, ∀ i,
      coordinates p r x i = algebraMap (K p r) (L p r) (b i) +
        algebraMap (K p r) (L p r) s * a p r i :=
  RigidDenseSource.mem_source (K p r) (a p r)

theorem mem_source (x : A p r) : x ∈ source p r ↔
    ∃ b : Fin p → K p r, ∃ s : K p r,
      x = (∑ i : Fin p, b i • TruncatedPolynomial.epsilon (L p r) p ^ (i : ℕ)) +
        s • vector p r := by
  rw [mem_source_coordinates]
  constructor
  · rintro ⟨b, s, h⟩
    refine ⟨b, s, ?_⟩
    have hx : coordinates p r x =
        RigidDenseSource.coordinateMap (K p r) (L p r) (Fin p) b + s • a p r := by
      ext i
      simpa [Algebra.smul_def] using h i
    apply (coordinates p r).injective
    rw [hx, map_add, map_smul]
    congr 1
    · apply (coordinates p r).symm.injective
      rw [LinearIsometryEquiv.symm_apply_apply]
      change (TruncatedPolynomial.coefficientIsometry (L p r) p).symm
        (RigidDenseSource.coordinateMap (K p r) (L p r) (Fin p) b) = _
      rw [TruncatedPolynomial.coefficientIsometry_symm_apply]
      simp only [RigidDenseSource.coordinateMap_apply, algebraMap_smul]
    · simp [vector]
  · rintro ⟨b, s, rfl⟩
    refine ⟨b, s, ?_⟩
    have hb : (∑ i : Fin p, b i • TruncatedPolynomial.epsilon (L p r) p ^ (i : ℕ)) =
        (coordinates p r).symm
          (RigidDenseSource.coordinateMap (K p r) (L p r) (Fin p) b) := by
      symm
      change (TruncatedPolynomial.coefficientIsometry (L p r) p).symm
        (RigidDenseSource.coordinateMap (K p r) (L p r) (Fin p) b) = _
      simpa only [RigidDenseSource.coordinateMap_apply, algebraMap_smul] using
        TruncatedPolynomial.coefficientIsometry_symm_apply (L p r) p
          (RigidDenseSource.coordinateMap (K p r) (L p r) (Fin p) b)
    rw [hb, map_add, map_smul]
    simp [vector, Algebra.smul_def]

theorem finrank_source : Module.finrank (K p r) (source p r) = p + 1 := by
  rw [(sourceEquiv p r).toLinearEquiv.finrank_eq,
    RigidDenseSource.finrank_source (K p r) (a p r) (algebraicIndependent_a p r)]
  simp

instance finiteDimensional_source : Module.Finite (K p r) (source p r) :=
  Module.Finite.equiv (sourceEquiv p r).symm.toLinearEquiv

instance nontrivial_source : Nontrivial (source p r) :=
  (sourceEquiv p r).toEquiv.nontrivial

/-- The actual quotient powers belong to the literal source. -/
def standard (i : Fin p) : source p r :=
  (sourceEquiv p r).symm (RigidDenseSource.standard (K p r) (a p r) i)

@[simp] theorem coe_standard (i : Fin p) :
    (standard p r i : A p r) = TruncatedPolynomial.epsilon (L p r) p ^ (i : ℕ) := by
  apply (coordinates p r).injective
  change coordinates p r ((coordinates p r).symm (Pi.single i 1)) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  ext j
  change (Pi.single i (1 : L p r) : Fin p → L p r) j = TruncatedPolynomial.coeff (L p r) p
    (TruncatedPolynomial.epsilon (L p r) p ^ (i : ℕ)) j
  rw [TruncatedPolynomial.coeff_pow]
  simp [Pi.single_apply, Fin.ext_iff, eq_comm]

@[simp] theorem norm_standard (i : Fin p) : ‖standard p r i‖ = 1 := by
  rw [← (sourceEquiv p r).norm_map]
  simpa only [standard, LinearIsometryEquiv.apply_symm_apply] using
    RigidDenseSource.norm_standard (K p r) (a p r) i

theorem denseRange_subtype : DenseRange (source p r).subtypeₗᵢ := by
  have hd := RigidDenseSource.denseRange_subtype (a := a p r)
    (RationalField.denseRange_algebraMap (ZMod p) r)
  have ht := (coordinates p r).symm.surjective.denseRange.comp hd
    (coordinates p r).symm.continuous
  apply ht.mono
  rintro _ ⟨x, rfl⟩
  exact ⟨(sourceEquiv p r).symm x, rfl⟩

theorem norm_source (x : source p r) :
    ‖x‖ = (Finset.univ.sup fun i : Fin p =>
      ‖TruncatedPolynomial.coeff (L p r) p x i‖₊ : ℝ≥0) := rfl

/-- Rigidity transports along the same exact coefficient isometry. -/
theorem existsUnique_scalar (T : source p r →L[K p r] source p r) :
    ∃! s : K p r, ∀ x, T x = s • x := by
  let e := (sourceEquiv p r).toContinuousLinearEquiv
  let U := e.toContinuousLinearMap.comp (T.comp e.symm.toContinuousLinearMap)
  obtain ⟨s, hs, hu⟩ := RigidDenseSource.existsUnique_scalar
    (RationalField.denseRange_algebraMap (ZMod p) r) (algebraicIndependent_a p r) U
  refine ⟨s, ?_, ?_⟩
  · intro x
    apply e.injective
    simpa [U] using hs (e x)
  · intro t ht
    apply hu t
    intro y
    simp [U, ht]

theorem exists_scalar (T : source p r →L[K p r] source p r) :
    ∃ s : K p r, ∀ x, T x = s • x :=
  (existsUnique_scalar p r T).exists

/-- Every bounded functional to the actual incomplete rational field vanishes. -/
theorem dual_eq_zero (f : source p r →L[K p r] K p r) : f = 0 := by
  have h := RigidDenseSource.dual_eq_zero
    (RationalField.denseRange_algebraMap (ZMod p) r) (algebraicIndependent_a p r)
    (f.comp (sourceEquiv p r).symm.toContinuousLinearEquiv.toContinuousLinearMap)
  ext x
  have hx := congrArg (fun f => f (sourceEquiv p r x)) h
  simpa using hx

/-- Isometric scalar coordinates on the literal source's bounded endomorphisms. -/
def endScalarEquiv : (source p r →L[K p r] source p r) ≃ₗᵢ[K p r] K p r :=
  endScalarEquivOfRigidity (exists_scalar p r)

theorem endScalarEquiv_apply (T : source p r →L[K p r] source p r) (x : source p r) :
    T x = endScalarEquiv p r T • x :=
  endScalarEquivOfRigidity_apply (exists_scalar p r) T x

@[simp] theorem endScalarEquiv_symm_apply (s : K p r) :
    (endScalarEquiv p r).symm s = s • ContinuousLinearMap.id (K p r) (source p r) :=
  endScalarEquivOfRigidity_symm_apply (exists_scalar p r) s

@[simp] theorem norm_endScalarEquiv (T : source p r →L[K p r] source p r) :
    ‖endScalarEquiv p r T‖ = ‖T‖ := (endScalarEquiv p r).norm_map T

@[simp] theorem norm_scalar_id (s : K p r) :
    ‖s • ContinuousLinearMap.id (K p r) (source p r)‖ = ‖s‖ := by
  simpa only [scalarActionIsometry_apply] using
    (scalarActionIsometry (K := K p r) (E := source p r)).norm_map s

@[simp] theorem endScalarEquiv_id :
    endScalarEquiv p r (ContinuousLinearMap.id (K p r) (source p r)) = 1 :=
  endScalarEquivOfRigidity_id (exists_scalar p r)

@[simp] theorem endScalarEquiv_comp (T U : source p r →L[K p r] source p r) :
    endScalarEquiv p r (T.comp U) = endScalarEquiv p r T * endScalarEquiv p r U :=
  endScalarEquivOfRigidity_comp (exists_scalar p r) T U

end AlternatingAnalytic.RigidDenseSource.Concrete
