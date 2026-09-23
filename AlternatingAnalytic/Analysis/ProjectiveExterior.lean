import AlternatingAnalytic.Algebra.DeterminantArray
import Mathlib.Analysis.Normed.Module.PiTensorProduct.ProjectiveSeminorm
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Module.Completion

/-!
# The ordinary-sum projective exterior norm and completion

Finite wedge decompositions define the ordinary-sum projective norm on exterior powers
of bounded functions. Determinant coordinates prove positivity and give a contraction.
The Banach completion carries the canonical continuous alternating wedge map and the
continuous extension of the determinant map.
-/

namespace AlternatingAnalytic

open Module
open scoped BoundedContinuousFunction

variable {K : Type*} [NormedField K]
  {V : Type*} [SeminormedAddCommGroup V] [NormedSpace K V] {k : ℕ}

/-- Evaluate a finite list of scalar multiples of pure wedges. -/
noncomputable def exteriorDecompositionValue :
    FreeAddMonoid (K × (Fin k → V)) →+ (⋀[K]^k V) :=
  FreeAddMonoid.lift fun p ↦ p.1 • exteriorPower.ιMulti K k p.2

/-- Multiplying all coefficients scales the represented exterior vector. -/
theorem exteriorDecompositionValue_smul (p : FreeAddMonoid (K × (Fin k → V))) (a : K) :
    exteriorDecompositionValue (p.map fun y ↦ (a * y.1, y.2)) =
      a • exteriorDecompositionValue p := by
  simp [exteriorDecompositionValue, FreeAddMonoid.lift_apply,
    Function.comp_def, mul_smul, List.smul_sum]

/-- Every exterior vector admits a finite weighted wedge decomposition. -/
theorem exists_exterior_decomposition (ω : ⋀[K]^k V) :
    ∃ p : FreeAddMonoid (K × (Fin k → V)), exteriorDecompositionValue p = ω := by
  have hω : ω ∈ Submodule.span K (Set.range (exteriorPower.ιMulti K k)) := by
    rw [exteriorPower.ιMulti_span]
    exact Submodule.mem_top
  induction hω using Submodule.span_induction with
  | mem _ hx =>
    obtain ⟨x, rfl⟩ := hx
    exact ⟨FreeAddMonoid.of (1, x), by simp [exteriorDecompositionValue]⟩
  | zero => exact ⟨0, map_zero _⟩
  | add ω η _ _ hω hη =>
    obtain ⟨p, rfl⟩ := hω
    obtain ⟨q, rfl⟩ := hη
    exact ⟨p + q, map_add _ _ _⟩
  | smul a ω _ hω =>
    obtain ⟨p, rfl⟩ := hω
    exact ⟨_, exteriorDecompositionValue_smul p a⟩

/-- The admissible finite weighted decompositions of an exterior vector. -/
def exteriorDecompositions (ω : ⋀[K]^k V) :
    Set (FreeAddMonoid (K × (Fin k → V))) :=
  {p | exteriorDecompositionValue p = ω}

instance (ω : ⋀[K]^k V) : Nonempty (exteriorDecompositions ω) :=
  nonempty_subtype.mpr (exists_exterior_decomposition ω)

/-- The ordinary sum of the products of norms in a weighted wedge decomposition. -/
def exteriorDecompositionCost (p : FreeAddMonoid (K × (Fin k → V))) : ℝ :=
  PiTensorProduct.projectiveSeminormAux p

omit [NormedSpace K V] in
theorem exteriorDecompositionCost_nonneg (p : FreeAddMonoid (K × (Fin k → V))) :
    0 ≤ exteriorDecompositionCost p := PiTensorProduct.projectiveSeminormAux_nonneg p

theorem exteriorDecompositionCost_bddBelow (ω : ⋀[K]^k V) :
    BddBelow (Set.range fun p : exteriorDecompositions ω ↦ exteriorDecompositionCost p.val) :=
  ⟨0, by rintro _ ⟨p, rfl⟩; exact exteriorDecompositionCost_nonneg p.val⟩

/-- The infimum of the ordinary-sum costs of all finite weighted wedge decompositions. -/
noncomputable def projectiveExteriorSeminormFun (ω : ⋀[K]^k V) : ℝ :=
  ⨅ p : exteriorDecompositions ω, exteriorDecompositionCost p.val

theorem projectiveExteriorSeminormFun_zero :
    projectiveExteriorSeminormFun (0 : ⋀[K]^k V) = 0 := by
  apply le_antisymm
  · exact (ciInf_le (exteriorDecompositionCost_bddBelow _) ⟨0, map_zero _⟩).trans_eq rfl
  · exact le_ciInf fun p ↦ exteriorDecompositionCost_nonneg p.val

theorem projectiveExteriorSeminormFun_add_le (ω η : ⋀[K]^k V) :
    projectiveExteriorSeminormFun (ω + η) ≤
      projectiveExteriorSeminormFun ω + projectiveExteriorSeminormFun η := by
  apply le_ciInf_add_ciInf
  intro p q
  refine ciInf_le_of_le (exteriorDecompositionCost_bddBelow _) ⟨p.val + q.val, ?_⟩ ?_
  · change exteriorDecompositionValue (p.val + q.val) = ω + η
    rw [map_add, p.property, q.property]
  · exact PiTensorProduct.projectiveSeminormAux_add_le _ _

theorem projectiveExteriorSeminormFun_smul_le (a : K) (ω : ⋀[K]^k V) :
    projectiveExteriorSeminormFun (a • ω) ≤ ‖a‖ * projectiveExteriorSeminormFun ω := by
  simp only [projectiveExteriorSeminormFun, Real.mul_iInf_of_nonneg (norm_nonneg _)]
  apply le_ciInf
  intro p
  refine ciInf_le_of_le (exteriorDecompositionCost_bddBelow _)
    ⟨p.val.map (fun y ↦ (a * y.1, y.2)), ?_⟩ ?_
  · change exteriorDecompositionValue _ = a • ω
    rw [exteriorDecompositionValue_smul, p.property]
  · exact (PiTensorProduct.projectiveSeminormAux_smul p.val a).le

/-- The projective exterior seminorm, using ordinary sums rather than maxima. -/
noncomputable def projectiveExteriorSeminorm : Seminorm K (⋀[K]^k V) :=
  Seminorm.ofSMulLE projectiveExteriorSeminormFun projectiveExteriorSeminormFun_zero
    projectiveExteriorSeminormFun_add_le projectiveExteriorSeminormFun_smul_le

theorem projectiveExteriorSeminorm_def (ω : ⋀[K]^k V) :
    projectiveExteriorSeminorm ω =
      ⨅ p : exteriorDecompositions ω, exteriorDecompositionCost p.val := rfl

/-- The projective seminorm is bounded by the product of norms on a pure wedge. -/
theorem projectiveExteriorSeminorm_ιMulti_le (x : Fin k → V) :
    projectiveExteriorSeminorm (exteriorPower.ιMulti K k x) ≤ ∏ i, ‖x i‖ := by
  have h := ciInf_le (exteriorDecompositionCost_bddBelow (exteriorPower.ιMulti K k x))
    ⟨FreeAddMonoid.of (1, x), by simp [exteriorDecompositions, exteriorDecompositionValue]⟩
  simpa [projectiveExteriorSeminorm_def, exteriorDecompositionCost,
    PiTensorProduct.projectiveSeminormAux] using h

/-- The value of a finite unweighted sum of pure wedges. -/
noncomputable def exteriorWedgeSum : FreeAddMonoid (Fin k → V) →+ (⋀[K]^k V) :=
  FreeAddMonoid.lift (exteriorPower.ιMulti K k)

/-- The ordinary sum of the products of the factor norms. -/
def exteriorWedgeCost (q : FreeAddMonoid (Fin k → V)) : ℝ :=
  (q.toList.map fun x ↦ ∏ i, ‖x i‖).sum

theorem exteriorWedgeCost_nonneg (q : FreeAddMonoid (Fin k → V)) :
    0 ≤ exteriorWedgeCost q := by
  apply List.sum_nonneg
  intro r hr
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
  exact Finset.prod_nonneg fun _ _ ↦ norm_nonneg _

theorem prod_norm_update_smul (α : Fin k) (a : K) (x : Fin k → V) :
    (∏ i, ‖Function.update x α (a • x α) i‖) = ‖a‖ * ∏ i, ‖x i‖ := by
  simp_rw [Function.apply_update (fun _ ↦ norm)]
  rw [Finset.prod_update_of_mem (Finset.mem_univ α), norm_smul]
  simp only [Finset.sdiff_singleton_eq_erase]
  rw [mul_assoc, mul_comm ‖x α‖, Finset.prod_erase_mul _ _ (Finset.mem_univ α)]

theorem exteriorWedgeSum_absorb (α : Fin k) (p : FreeAddMonoid (K × (Fin k → V))) :
    exteriorWedgeSum (p.map fun y ↦ Function.update y.2 α (y.1 • y.2 α)) =
      exteriorDecompositionValue p := by
  simp [exteriorWedgeSum, exteriorDecompositionValue, FreeAddMonoid.lift_apply,
    Function.comp_def]

theorem exteriorWedgeCost_absorb (α : Fin k) (p : FreeAddMonoid (K × (Fin k → V))) :
    exteriorWedgeCost (p.map fun y ↦ Function.update y.2 α (y.1 • y.2 α)) =
      exteriorDecompositionCost p := by
  simp [exteriorWedgeCost, exteriorDecompositionCost, PiTensorProduct.projectiveSeminormAux,
    Function.comp_def, prod_norm_update_smul]

/-- In positive degree the seminorm is exactly the infimum over finite unweighted
sums of pure wedges, with the ordinary sum of products as cost. -/
theorem projectiveExteriorSeminorm_eq_iInf_wedgeCost (α : Fin k) (ω : ⋀[K]^k V) :
    projectiveExteriorSeminorm ω =
      ⨅ q : {q : FreeAddMonoid (Fin k → V) // exteriorWedgeSum q = ω},
        exteriorWedgeCost q.val := by
  have hex : Nonempty {q : FreeAddMonoid (Fin k → V) // exteriorWedgeSum q = ω} := by
    obtain ⟨p, hp⟩ := exists_exterior_decomposition ω
    exact ⟨⟨_, (exteriorWedgeSum_absorb α p).trans hp⟩⟩
  have hb : BddBelow (Set.range fun q :
      {q : FreeAddMonoid (Fin k → V) // exteriorWedgeSum q = ω} ↦ exteriorWedgeCost q.val) :=
    ⟨0, by rintro _ ⟨q, rfl⟩; exact exteriorWedgeCost_nonneg q.val⟩
  apply le_antisymm
  · apply le_ciInf
    intro q
    refine ciInf_le_of_le (exteriorDecompositionCost_bddBelow _)
      ⟨q.val.map (fun x ↦ (1, x)), ?_⟩ ?_
    · change exteriorDecompositionValue _ = ω
      simpa [exteriorDecompositionValue, exteriorWedgeSum, FreeAddMonoid.lift_apply,
        Function.comp_def] using q.property
    · simp [exteriorDecompositionCost, exteriorWedgeCost,
        PiTensorProduct.projectiveSeminormAux, Function.comp_def]
  · apply le_ciInf
    intro p
    refine ciInf_le_of_le hb ⟨_, (exteriorWedgeSum_absorb α p.val).trans p.property⟩ ?_
    exact (exteriorWedgeCost_absorb α p.val).le

variable {S : Type*}

/-- The determinant array induced by an injective coordinate representation. -/
noncomputable def coordinateExteriorArray (e : V →ₗ[K] (S → K)) :
    (⋀[K]^k V) →ₗ[K] ((Fin k → S) → K) :=
  determinantArray.comp (exteriorPower.map k e)

theorem coordinateExteriorArray_ιMulti (e : V →ₗ[K] (S → K))
    (x : Fin k → V) (c : Fin k → S) :
    coordinateExteriorArray e (exteriorPower.ιMulti K k x) c =
      Matrix.det (fun i j ↦ e (x j) (c i)) := by
  simp only [coordinateExteriorArray, LinearMap.comp_apply,
    exteriorPower.map_apply_ιMulti, determinantArray_ιMulti, Function.comp_apply]

theorem coordinateExteriorArray_injective (e : V →ₗ[K] (S → K))
    (he : Function.Injective e) : Function.Injective (coordinateExteriorArray (k := k) e) :=
  determinantArray_injective.comp (exteriorPower.map_injective_field he)

variable [IsUltrametricDist K]

/-- Over an ultrametric field, every pure-wedge determinant coordinate is bounded by
the product of the factor norms, with no factorial factor. -/
theorem norm_coordinateExteriorArray_ιMulti_le (e : V →ₗ[K] (S → K))
    (he : ∀ v s, ‖e v s‖ ≤ ‖v‖) (x : Fin k → V) (c : Fin k → S) :
    ‖coordinateExteriorArray e (exteriorPower.ιMulti K k x) c‖ ≤ ∏ i, ‖x i‖ := by
  classical
  rw [coordinateExteriorArray_ιMulti]
  change ‖(Matrix.of (fun i j ↦ e (x j) (c i))).det‖ ≤ _
  rw [Matrix.det_apply]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)
  intro σ hσ
  rw [norm_units_zsmul, norm_prod]
  exact Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun i _ ↦ he (x i) (c (σ i)))

/-- Each determinant coordinate is bounded by the cost of every decomposition. -/
theorem norm_coordinateExteriorArray_decomposition_le (e : V →ₗ[K] (S → K))
    (he : ∀ v s, ‖e v s‖ ≤ ‖v‖) (p : FreeAddMonoid (K × (Fin k → V)))
    (c : Fin k → S) :
    ‖coordinateExteriorArray e (exteriorDecompositionValue p) c‖ ≤
      exteriorDecompositionCost p := by
  induction p using FreeAddMonoid.inductionOn' with
  | zero => simp [exteriorDecompositionCost, PiTensorProduct.projectiveSeminormAux]
  | of_add b p ih =>
    simp only [map_add, exteriorDecompositionValue, FreeAddMonoid.lift_eval_of,
      map_smul, Pi.add_apply, Pi.smul_apply]
    calc
      _ ≤ ‖b.1 • coordinateExteriorArray e (exteriorPower.ιMulti K k b.2) c‖ +
          ‖coordinateExteriorArray e (exteriorDecompositionValue p) c‖ := norm_add_le _ _
      _ ≤ ‖b.1‖ * (∏ i, ‖b.2 i‖) + exteriorDecompositionCost p := by
        rw [norm_smul]
        exact add_le_add (mul_le_mul_of_nonneg_left
          (norm_coordinateExteriorArray_ιMulti_le e he b.2 c) (norm_nonneg _)) ih
      _ = _ := by simp [exteriorDecompositionCost, PiTensorProduct.projectiveSeminormAux]

/-- The determinant coordinates are bounded by the projective exterior seminorm. -/
theorem norm_coordinateExteriorArray_le (e : V →ₗ[K] (S → K))
    (he : ∀ v s, ‖e v s‖ ≤ ‖v‖) (ω : ⋀[K]^k V) (c : Fin k → S) :
    ‖coordinateExteriorArray e ω c‖ ≤ projectiveExteriorSeminorm ω := by
  apply le_ciInf
  intro p
  have hp : exteriorDecompositionValue p.val = ω := p.property
  simpa only [hp] using norm_coordinateExteriorArray_decomposition_le e he p.val c

/-- Injective bounded coordinates make the projective exterior seminorm a genuine norm. -/
theorem projectiveExteriorSeminorm_eq_zero_iff (e : V →ₗ[K] (S → K))
    (hinj : Function.Injective e) (he : ∀ v s, ‖e v s‖ ≤ ‖v‖) (ω : ⋀[K]^k V) :
    projectiveExteriorSeminorm ω = 0 ↔ ω = 0 := by
  constructor
  · intro hω
    apply coordinateExteriorArray_injective e hinj
    ext c
    rw [map_zero, Pi.zero_apply]
    exact norm_eq_zero.mp (le_antisymm ((norm_coordinateExteriorArray_le e he ω c).trans_eq hω)
      (norm_nonneg _))
  · rintro rfl
    exact map_zero _

/-- The genuine projective exterior group norm, certified by injective bounded coordinates. -/
noncomputable def projectiveExteriorAddGroupNorm (e : V →ₗ[K] (S → K))
    (hinj : Function.Injective e) (he : ∀ v s, ‖e v s‖ ≤ ‖v‖) :
    AddGroupNorm (⋀[K]^k V) where
  __ := projectiveExteriorSeminorm.toAddGroupSeminorm
  eq_zero_of_map_eq_zero' ω h := (projectiveExteriorSeminorm_eq_zero_iff e hinj he ω).mp h

/-- Bounded continuous functions have their ordinary injective coordinate representation. -/
def boundedFunctionCoordinates [TopologicalSpace S] : (S →ᵇ K) →ₗ[K] (S → K) where
  toFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [IsUltrametricDist K] in
@[simp]
theorem boundedFunctionCoordinates_apply [TopologicalSpace S] (f : S →ᵇ K) (s : S) :
    boundedFunctionCoordinates (K := K) f s = f s := rfl

omit [IsUltrametricDist K] in
theorem boundedFunctionCoordinates_injective [TopologicalSpace S] :
    Function.Injective (boundedFunctionCoordinates (K := K) (S := S)) := by
  intro f g h
  exact DFunLike.coe_injective h

/-- For bounded functions, the projective exterior seminorm is a genuine norm. -/
theorem boundedFunction_projectiveExteriorSeminorm_eq_zero_iff [TopologicalSpace S]
    (ω : ⋀[K]^k (S →ᵇ K)) : projectiveExteriorSeminorm ω = 0 ↔ ω = 0 :=
  projectiveExteriorSeminorm_eq_zero_iff boundedFunctionCoordinates
    boundedFunctionCoordinates_injective (fun f s ↦ f.norm_coe_le_norm s) ω

section DiscreteCoordinates

variable [TopologicalSpace S] [DiscreteTopology S]

/-- The bounded determinant array, with the ordinary supremum norm in its target. -/
noncomputable def boundedExteriorArray (e : V →ₗ[K] (S → K))
    (he : ∀ v s, ‖e v s‖ ≤ ‖v‖) :
    (⋀[K]^k V) →ₗ[K] ((Fin k → S) →ᵇ K) where
  toFun ω := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (coordinateExteriorArray e ω) (projectiveExteriorSeminorm ω)
    (norm_coordinateExteriorArray_le e he ω)
  map_add' ω η := by ext c; exact congrFun (map_add (coordinateExteriorArray e) ω η) c
  map_smul' a ω := by ext c; exact congrFun (map_smul (coordinateExteriorArray e) a ω) c

theorem boundedExteriorArray_norm_le (e : V →ₗ[K] (S → K))
    (he : ∀ v s, ‖e v s‖ ≤ ‖v‖) (ω : ⋀[K]^k V) :
    ‖boundedExteriorArray e he ω‖ ≤ projectiveExteriorSeminorm ω :=
  (BoundedContinuousFunction.norm_le (apply_nonneg projectiveExteriorSeminorm ω)).mpr
    (norm_coordinateExteriorArray_le e he ω)

theorem boundedExteriorArray_injective (e : V →ₗ[K] (S → K))
    (hinj : Function.Injective e) (he : ∀ v s, ‖e v s‖ ≤ ‖v‖) :
    Function.Injective (boundedExteriorArray (k := k) e he) := by
  intro ω η h
  apply coordinateExteriorArray_injective e hinj
  exact congrArg (fun f : (Fin k → S) →ᵇ K ↦ (f : (Fin k → S) → K)) h

/-- The exact infimum formula, wedge estimate, bounded determinant estimate, and
positivity for exterior powers of the bounded-function space. -/
theorem boundedFunction_projectiveExterior_properties (α : Fin k) :
    (∀ ω : ⋀[K]^k (S →ᵇ K), projectiveExteriorSeminorm ω =
      ⨅ q : {q : FreeAddMonoid (Fin k → (S →ᵇ K)) // exteriorWedgeSum q = ω},
        exteriorWedgeCost q.val) ∧
    (∀ x : Fin k → (S →ᵇ K),
      projectiveExteriorSeminorm (exteriorPower.ιMulti K k x) ≤ ∏ i, ‖x i‖) ∧
    (∀ ω : ⋀[K]^k (S →ᵇ K),
      ‖boundedExteriorArray boundedFunctionCoordinates (fun f s ↦ f.norm_coe_le_norm s) ω‖ ≤
        projectiveExteriorSeminorm ω) ∧
    Function.Injective (boundedExteriorArray (k := k) (boundedFunctionCoordinates (K := K) (S := S))
      (fun f s ↦ f.norm_coe_le_norm s)) ∧
    (∀ ω : ⋀[K]^k (S →ᵇ K), projectiveExteriorSeminorm ω = 0 ↔ ω = 0) := by
  exact ⟨projectiveExteriorSeminorm_eq_iInf_wedgeCost α,
    projectiveExteriorSeminorm_ιMulti_le, boundedExteriorArray_norm_le _ _,
    boundedExteriorArray_injective _ boundedFunctionCoordinates_injective _,
    boundedFunction_projectiveExteriorSeminorm_eq_zero_iff⟩

end DiscreteCoordinates

end AlternatingAnalytic

namespace AlternatingAnalytic

open Module
open scoped BoundedContinuousFunction

variable (K : Type*) [NontriviallyNormedField K] (S : Type*) [TopologicalSpace S] (k : ℕ)

/-- The exterior power of bounded functions, carrying the ordinary-sum projective norm. -/
def ProjectiveExterior : Type _ := ⋀[K]^k (S →ᵇ K)

namespace ProjectiveExterior

variable [IsUltrametricDist K]

noncomputable instance : NormedAddCommGroup (ProjectiveExterior K S k) :=
  (projectiveExteriorAddGroupNorm (k := k) boundedFunctionCoordinates
    boundedFunctionCoordinates_injective (fun f s ↦ f.norm_coe_le_norm s)).toNormedAddCommGroup

noncomputable instance : Module K (ProjectiveExterior K S k) :=
  inferInstanceAs (Module K (⋀[K]^k (S →ᵇ K)))

noncomputable instance : NormedSpace K (ProjectiveExterior K S k) :=
  { (inferInstance : Module K (ProjectiveExterior K S k)) with
    norm_smul_le := fun a ω ↦ (map_smul_eq_mul projectiveExteriorSeminorm a ω).le }

theorem norm_eq (ω : ProjectiveExterior K S k) :
    ‖ω‖ = projectiveExteriorSeminorm (show ⋀[K]^k (S →ᵇ K) from ω) := rfl

end ProjectiveExterior

variable [IsUltrametricDist K]

/-- The canonical alternating wedge map into the normed exterior power. -/
noncomputable def projectiveExteriorWedge : (S →ᵇ K) [⋀^Fin k]→L[K] ProjectiveExterior K S k :=
  (show AlternatingMap K (S →ᵇ K) (ProjectiveExterior K S k) (Fin k) from
    exteriorPower.ιMulti K k).mkContinuous 1
      (fun x ↦ by
        change projectiveExteriorSeminorm (exteriorPower.ιMulti K k x) ≤ 1 * ∏ i, ‖x i‖
        simpa only [one_mul] using projectiveExteriorSeminorm_ιMulti_le x)

@[simp]
theorem projectiveExteriorWedge_apply (x : Fin k → (S →ᵇ K)) :
    (show ⋀[K]^k (S →ᵇ K) from projectiveExteriorWedge K S k x) =
      exteriorPower.ιMulti K k x := rfl

theorem projectiveExteriorWedge_norm_le : ‖projectiveExteriorWedge K S k‖ ≤ 1 :=
  AlternatingMap.mkContinuous_norm_le _ zero_le_one _

variable [DiscreteTopology S]

set_option maxHeartbeats 800000 in
/-- The determinant array as a bounded linear map on the projective exterior power. -/
noncomputable def projectiveExteriorArray :
    ProjectiveExterior K S k →L[K] ((Fin k → S) →ᵇ K) :=
  (show ProjectiveExterior K S k →ₗ[K] ((Fin k → S) →ᵇ K) from
    boundedExteriorArray boundedFunctionCoordinates (fun f s ↦ f.norm_coe_le_norm s)).mkContinuous 1
      (fun ω ↦ by
        change ‖boundedExteriorArray (k := k) (boundedFunctionCoordinates (K := K) (S := S))
          (fun f s ↦ f.norm_coe_le_norm s) ω‖ ≤ 1 * projectiveExteriorSeminorm ω
        simpa only [one_mul] using
          boundedExteriorArray_norm_le (boundedFunctionCoordinates (K := K) (S := S))
            (fun f s ↦ f.norm_coe_le_norm s) ω)

theorem projectiveExteriorArray_norm_le : ‖projectiveExteriorArray K S k‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem projectiveExteriorArray_injective : Function.Injective (projectiveExteriorArray K S k) :=
  boundedExteriorArray_injective (boundedFunctionCoordinates (K := K) (S := S))
    boundedFunctionCoordinates_injective
    (fun f s ↦ f.norm_coe_le_norm s)

@[simp]
theorem projectiveExteriorArray_apply (ω : ProjectiveExterior K S k) (c : Fin k → S) :
    projectiveExteriorArray K S k ω c =
      coordinateExteriorArray (boundedFunctionCoordinates (K := K) (S := S)) ω c := rfl

set_option maxHeartbeats 800000 in
theorem projectiveExteriorArray_wedge (x : Fin k → (S →ᵇ K)) (c : Fin k → S) :
    projectiveExteriorArray K S k (projectiveExteriorWedge K S k x) c =
      Matrix.det (fun i j ↦ x j (c i)) := by
  change coordinateExteriorArray (boundedFunctionCoordinates (K := K) (S := S))
    (exteriorPower.ιMulti K k x) c = _
  simpa only [boundedFunctionCoordinates_apply] using
    coordinateExteriorArray_ιMulti (boundedFunctionCoordinates (K := K) (S := S)) x c

/-- The Banach completion of the projective exterior power. -/
abbrev ProjectiveExteriorCompletion := UniformSpace.Completion (ProjectiveExterior K S k)

/-- The canonical continuous alternating wedge map into the Banach completion. -/
noncomputable def completedExteriorWedge :
    (S →ᵇ K) [⋀^Fin k]→L[K] ProjectiveExteriorCompletion K S k :=
  (UniformSpace.Completion.toComplL : ProjectiveExterior K S k →L[K] _).compContinuousAlternatingMap
    (projectiveExteriorWedge K S k)

omit [DiscreteTopology S] in
theorem completedExteriorWedge_norm_le : ‖completedExteriorWedge K S k‖ ≤ 1 := by
  apply ContinuousAlternatingMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖((projectiveExteriorWedge K S k x : ProjectiveExterior K S k) :
    ProjectiveExteriorCompletion K S k)‖ ≤ _
  rw [UniformSpace.Completion.norm_coe, one_mul]
  rw [ProjectiveExterior.norm_eq]
  exact projectiveExteriorSeminorm_ιMulti_le x

variable [CompleteSpace K]

/-- The continuous extension of the determinant array to the projective completion. -/
noncomputable def completedExteriorArray :
    ProjectiveExteriorCompletion K S k →L[K] ((Fin k → S) →ᵇ K) :=
  (projectiveExteriorArray K S k).fromCompletion

theorem norm_completedExteriorArray_le (ω : ProjectiveExteriorCompletion K S k) :
    ‖completedExteriorArray K S k ω‖ ≤ ‖ω‖ := by
  induction ω using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (ContinuousLinearMap.continuous _).norm continuous_norm
  | ih ω =>
    simpa only [completedExteriorArray, ContinuousLinearMap.fromCompletion_apply_coe,
      UniformSpace.Completion.norm_coe, one_mul] using
      (projectiveExteriorArray K S k).le_of_opNorm_le
        (projectiveExteriorArray_norm_le K S k) ω

theorem completedExteriorArray_norm_le : ‖completedExteriorArray K S k‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro ω
  simpa only [one_mul] using norm_completedExteriorArray_le K S k ω

/-- The completed determinant map has the original determinant values on pure wedges. -/
theorem completedExteriorArray_wedge (x : Fin k → (S →ᵇ K)) (c : Fin k → S) :
    completedExteriorArray K S k (completedExteriorWedge K S k x) c =
      Matrix.det (fun i j ↦ x j (c i)) := by
  change (projectiveExteriorArray K S k).fromCompletion
    ((projectiveExteriorWedge K S k x : ProjectiveExterior K S k) :
      ProjectiveExteriorCompletion K S k) c = _
  rw [ContinuousLinearMap.fromCompletion_apply_coe]
  exact projectiveExteriorArray_wedge K S k x c

/-- The bounded determinant embedding and the completed continuous alternating wedge map. -/
theorem projectiveExteriorCompletion_properties :
    Function.Injective (projectiveExteriorArray K S k) ∧
    ‖projectiveExteriorArray K S k‖ ≤ 1 ∧
    ‖completedExteriorWedge K S k‖ ≤ 1 ∧
    ‖completedExteriorArray K S k‖ ≤ 1 ∧
    (∀ (x : Fin k → (S →ᵇ K)) (c : Fin k → S),
      completedExteriorArray K S k (completedExteriorWedge K S k x) c =
        Matrix.det (fun i j ↦ x j (c i))) := by
  exact ⟨projectiveExteriorArray_injective K S k, projectiveExteriorArray_norm_le K S k,
    completedExteriorWedge_norm_le K S k, completedExteriorArray_norm_le K S k,
    completedExteriorArray_wedge K S k⟩

/-- The ordinary-sum projective norm formula, its determinant embedding, and the Banach
completion with the canonical continuous alternating wedge map. -/
theorem projectiveExterior_properties (α : Fin k) :
    (∀ ω : ProjectiveExterior K S k, ‖ω‖ =
      ⨅ q : {q : FreeAddMonoid (Fin k → (S →ᵇ K)) //
        exteriorWedgeSum q = (show ⋀[K]^k (S →ᵇ K) from ω)}, exteriorWedgeCost q.val) ∧
    (∀ x : Fin k → (S →ᵇ K), ‖projectiveExteriorWedge K S k x‖ ≤ ∏ i, ‖x i‖) ∧
    (∀ ω : ProjectiveExterior K S k, ‖ω‖ = 0 ↔ ω = 0) ∧
    Function.Injective (projectiveExteriorArray K S k) ∧
    ‖projectiveExteriorArray K S k‖ ≤ 1 ∧
    CompleteSpace (ProjectiveExteriorCompletion K S k) ∧
    ‖completedExteriorWedge K S k‖ ≤ 1 ∧
    ‖completedExteriorArray K S k‖ ≤ 1 ∧
    (∀ (x : Fin k → (S →ᵇ K)) (c : Fin k → S),
      completedExteriorArray K S k (completedExteriorWedge K S k x) c =
        Matrix.det (fun i j ↦ x j (c i))) := by
  refine ⟨?_, ?_, fun _ ↦ norm_eq_zero, projectiveExteriorArray_injective K S k,
    projectiveExteriorArray_norm_le K S k, inferInstance,
    completedExteriorWedge_norm_le K S k, completedExteriorArray_norm_le K S k,
    completedExteriorArray_wedge K S k⟩
  · intro ω
    rw [ProjectiveExterior.norm_eq]
    exact projectiveExteriorSeminorm_eq_iInf_wedgeCost α ω
  · intro x
    rw [ProjectiveExterior.norm_eq]
    exact projectiveExteriorSeminorm_ιMulti_le x

end AlternatingAnalytic
