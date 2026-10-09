import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Dependent c₀ sums

The space `c₀({E i})` of families `x i ∈ E i` with `‖x i‖ → 0`, defined as the
closed span of coordinate vectors in `lp E ∞` with the supremum norm. It is used
in Appendix G with `E n = T_(n+1)(P)`, so the coordinates `n < N` hold tensor
degrees 1 through `N`.
-/

noncomputable section

open Filter
open scoped Topology BigOperators ENNReal NNReal

section Construction

variable (K : Type*) {I : Type*} (E : I → Type*)
  [NontriviallyNormedField K] [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace K (E i)]

/-- The linear span of the dependent coordinate vectors in ℓ∞. -/
def dependentCZeroSpan : Submodule K (lp E ∞) := by
  classical
  exact Submodule.span K {x | ∃ i, ∃ v : E i, x = lp.single ∞ i v}

/-- The closed linear span of the dependent coordinate vectors in ℓ∞. -/
def dependentCZeroSubmodule : Submodule K (lp E ∞) :=
  (dependentCZeroSpan K E).topologicalClosure

/-- The dependent c₀ sum, with the norm inherited from dependent ℓ∞. -/
abbrev DependentCZero := ↥(dependentCZeroSubmodule K E)

namespace DependentCZero

variable {K E}

instance : CoeFun (DependentCZero K E) (fun _ => ∀ i, E i) :=
  ⟨fun x => (x.val : ∀ i, E i)⟩

@[ext]
theorem ext {x y : DependentCZero K E} (h : ∀ i, x i = y i) : x = y :=
  Subtype.ext (lp.ext (funext h))

@[simp] theorem zero_apply (i : I) : (0 : DependentCZero K E) i = 0 := rfl
@[simp] theorem add_apply (x y : DependentCZero K E) (i : I) :
    (x + y) i = x i + y i := rfl
@[simp] theorem sub_apply (x y : DependentCZero K E) (i : I) :
    (x - y) i = x i - y i := rfl
@[simp] theorem smul_apply (a : K) (x : DependentCZero K E) (i : I) :
    (a • x) i = a • x i := rfl

/-- The ambient inclusion is a linear isometry. -/
def toLp : DependentCZero K E →ₗᵢ[K] lp E ∞ :=
  (dependentCZeroSubmodule K E).subtypeₗᵢ

@[simp] theorem toLp_apply (x : DependentCZero K E) : toLp x = x.val := rfl

/-- The norm is the supremum of the coordinate norms (zero for an empty index type). -/
theorem norm_eq (x : DependentCZero K E) : ‖x‖ = ⨆ i, ‖x i‖ :=
  lp.norm_eq_ciSup x.val

theorem norm_apply_le_norm (x : DependentCZero K E) (i : I) : ‖x i‖ ≤ ‖x‖ :=
  lp.norm_apply_le_norm ENNReal.top_ne_zero x.val i

theorem norm_le {x : DependentCZero K E} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i, ‖x i‖ ≤ C) : ‖x‖ ≤ C :=
  lp.norm_le_of_forall_le hC h

instance [∀ i, CompleteSpace (E i)] : CompleteSpace (DependentCZero K E) :=
  inferInstanceAs (CompleteSpace (dependentCZeroSpan K E).topologicalClosure)

theorem single_mem (i : I) (v : E i) :
    letI := Classical.decEq I
    lp.single ∞ i v ∈ dependentCZeroSubmodule K E := by
  classical
  exact (dependentCZeroSpan K E).le_topologicalClosure
    (Submodule.subset_span ⟨i, v, rfl⟩)

/-- The coordinate injection, obtained by restricting the codomain of Mathlib's map. -/
def single (i : I) : E i →L[K] DependentCZero K E := by
  classical
  exact (lp.singleContinuousLinearMap K E ∞ i).codRestrict
    (dependentCZeroSubmodule K E) (single_mem i)

@[simp] theorem single_apply (i : I) (v : E i) (j : I) :
    letI := Classical.decEq I
    single (K := K) (E := E) i v j = Pi.single i v j := rfl

@[simp] theorem single_apply_self (i : I) (v : E i) :
    single (K := K) (E := E) i v i = v := by
  classical
  exact lp.single_apply_self ∞ i v

theorem single_apply_ne (i : I) (v : E i) {j : I} (h : j ≠ i) :
    single (K := K) (E := E) i v j = 0 := by
  classical
  exact lp.single_apply_ne ∞ i v h

@[simp] theorem norm_single (i : I) (v : E i) :
    ‖single (K := K) (E := E) i v‖ = ‖v‖ := by
  classical
  exact lp.norm_single (by simp) i v

theorem norm_single_le (i : I) : ‖single (K := K) (E := E) i‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun x => by rw [one_mul]; exact (norm_single i x).le)

/-- Coordinate projection, the restriction of Mathlib's evaluation map. -/
def eval (i : I) : DependentCZero K E →L[K] E i :=
  (lp.evalCLM K E ∞ i).comp (dependentCZeroSubmodule K E).subtypeL

@[simp] theorem eval_apply (i : I) (x : DependentCZero K E) : eval i x = x i := rfl

theorem norm_eval_le (i : I) : ‖eval (K := K) (E := E) i‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun x => by simpa using norm_apply_le_norm x i)

@[simp] theorem eval_comp_single (i : I) :
    (eval (K := K) (E := E) i).comp (single i) = ContinuousLinearMap.id K (E i) := by
  ext v
  exact single_apply_self (K := K) i v

theorem eval_comp_single_ne (i j : I) (h : i ≠ j) :
    (eval (K := K) (E := E) i).comp (single j) = 0 := by
  ext v
  exact single_apply_ne (K := K) j v h

/-- A finite vector with the prescribed dependent coordinates. -/
def finiteVector (s : Finset I) (v : ∀ i, E i) : DependentCZero K E :=
  ∑ i ∈ s, single i (v i)

@[simp] theorem finiteVector_apply (s : Finset I) (v : ∀ i, E i) (i : I) :
    letI := Classical.decEq I
    finiteVector (K := K) s v i = if i ∈ s then v i else 0 := by
  classical
  change eval i (∑ j ∈ s, single j (v j)) = _
  simp only [map_sum, eval_apply, single_apply, Finset.sum_pi_single]

/-- The norm of a finite vector is the maximum of its coordinate norms. -/
theorem nnnorm_finiteVector (s : Finset I) (v : ∀ i, E i) :
    ‖finiteVector (K := K) s v‖₊ = s.sup (fun i => ‖v i‖₊) := by
  classical
  apply le_antisymm
  · change ‖finiteVector (K := K) s v‖ ≤ ((s.sup (fun i => ‖v i‖₊) : ℝ≥0) : ℝ)
    apply norm_le (NNReal.coe_nonneg _)
    intro i
    by_cases hi : i ∈ s
    · simpa [finiteVector_apply, hi] using
        (show (‖v i‖₊ : ℝ) ≤ ((s.sup (fun i => ‖v i‖₊) : ℝ≥0) : ℝ) from
          NNReal.coe_le_coe.mpr (Finset.le_sup (f := fun i => ‖v i‖₊) hi))
    · simp [finiteVector_apply, hi]
  · apply Finset.sup_le
    intro i hi
    change ‖v i‖ ≤ ‖finiteVector (K := K) s v‖
    simpa [finiteVector_apply, hi] using norm_apply_le_norm (finiteVector (K := K) s v) i

/-- Finite-subset truncation as a continuous linear endomorphism. -/
def truncate (s : Finset I) : DependentCZero K E →L[K] DependentCZero K E :=
  ∑ i ∈ s, (single i).comp (eval i)

theorem truncate_eq_finiteVector (s : Finset I) (x : DependentCZero K E) :
    truncate s x = finiteVector s x := by
  simp [truncate, finiteVector]

@[simp] theorem truncate_apply (s : Finset I) (x : DependentCZero K E) (i : I) :
    letI := Classical.decEq I
    truncate s x i = if i ∈ s then x i else 0 := by
  classical
  rw [truncate_eq_finiteVector, finiteVector_apply]

theorem norm_truncate_apply_le (s : Finset I) (x : DependentCZero K E) :
    ‖truncate s x‖ ≤ ‖x‖ := by
  classical
  apply norm_le (norm_nonneg x)
  intro i
  by_cases hi : i ∈ s
  · simpa [hi] using norm_apply_le_norm x i
  · simp [hi]

theorem norm_truncate_le (s : Finset I) :
    ‖truncate (K := K) (E := E) s‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun x => by simpa using norm_truncate_apply_le s x)


/-- Every vector in the algebraic coordinate span has finite support. -/
theorem finite_support_of_mem_span (x : lp E ∞) (hx : x ∈ dependentCZeroSpan K E) :
    ∃ s : Finset I, ∀ i ∉ s, x i = 0 := by
  classical
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, v, rfl⟩ := hx
    refine ⟨{i}, fun j hj => ?_⟩
    exact lp.single_apply_ne _ _ _ (by simpa using hj)
  | zero => exact ⟨∅, by simp⟩
  | add x y hx hy hx' hy' =>
    obtain ⟨s, hs⟩ := hx'
    obtain ⟨t, ht⟩ := hy'
    refine ⟨s ∪ t, fun i hi => ?_⟩
    have his : i ∉ s := fun h => hi (Finset.mem_union_left _ h)
    have hit : i ∉ t := fun h => hi (Finset.mem_union_right _ h)
    simp [hs i his, ht i hit]
  | smul a x hx hx' =>
    obtain ⟨s, hs⟩ := hx'
    exact ⟨s, fun i hi => by simp [lp.coeFn_smul, hs i hi]⟩

/-- Coordinate formula for ambient finite truncations. -/
theorem ambient_sum_single_apply [DecidableEq I] (s : Finset I) (v : ∀ i, E i) (i : I) :
    (∑ j ∈ s, lp.single ∞ j (v j)) i = if i ∈ s then v i else 0 := by
  classical
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.single_apply, Finset.sum_pi_single]

/-- The closed coordinate span consists of the families with `‖x i‖ → 0` along `cofinite`. -/
theorem mem_iff (x : lp E ∞) :
    x ∈ dependentCZeroSubmodule K E ↔
      Tendsto (fun i => ‖x i‖) cofinite (𝓝 0) := by
  classical
  constructor
  · intro hx
    change x ∈ closure (dependentCZeroSpan K E : Set (lp E ∞)) at hx
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx ε hε
    obtain ⟨s, hs⟩ := finite_support_of_mem_span y hy
    filter_upwards [s.eventually_cofinite_notMem] with i hi
    have hbound := lp.norm_apply_le_norm (by simp : (∞ : ℝ≥0∞) ≠ 0) (x - y) i
    have hn : ‖x i‖ < ε := by
      have heq : (x - y) i = x i := by simp [hs i hi]
      rw [heq] at hbound
      exact lt_of_le_of_lt hbound (by simpa [dist_eq_norm] using hxy)
    simpa using hn
  · intro hx
    change x ∈ closure (dependentCZeroSpan K E : Set (lp E ∞))
    rw [Metric.mem_closure_iff]
    intro ε hε
    have he : ∀ᶠ i in cofinite, ‖x i‖ < ε / 2 :=
      hx.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 2))
    let s : Finset I := (eventually_cofinite.mp he).toFinset
    have hs : ∀ i ∉ s, ‖x i‖ < ε / 2 := by
      intro i hi
      simpa [s] using hi
    refine ⟨∑ i ∈ s, lp.single ∞ i (x i), ?_, ?_⟩
    · apply Submodule.sum_mem
      intro i hi
      exact Submodule.subset_span ⟨i, x i, rfl⟩
    · rw [dist_eq_norm]
      refine lt_of_le_of_lt (lp.norm_le_of_forall_le (by positivity) ?_) (half_lt_self hε)
      intro i
      rw [lp.coeFn_sub, Pi.sub_apply, ambient_sum_single_apply]
      split_ifs with hi
      · simpa using (le_of_lt (half_pos hε))
      · simpa using le_of_lt (hs i hi)

/-- Every c₀ vector has coordinate norms tending to zero along `cofinite`. -/
theorem tendsto_norm (x : DependentCZero K E) :
    Tendsto (fun i => ‖x i‖) cofinite (𝓝 0) :=
  (mem_iff x.val).mp x.property

/-- Finite-subset truncations converge in the inherited supremum norm. -/
theorem tendsto_truncate (x : DependentCZero K E) :
    Tendsto (fun s : Finset I => truncate s x) atTop (𝓝 x) := by
  classical
  rw [Metric.tendsto_atTop]
  intro ε hε
  have he : ∀ᶠ i in cofinite, ‖x i‖ < ε / 2 :=
    (tendsto_norm x).eventually (gt_mem_nhds (half_pos hε))
  let s : Finset I := (eventually_cofinite.mp he).toFinset
  have hs : ∀ i ∉ s, ‖x i‖ < ε / 2 := by
    intro i hi
    simpa [s] using hi
  refine ⟨s, fun t hst => ?_⟩
  rw [dist_eq_norm]
  refine lt_of_le_of_lt (norm_le (le_of_lt (half_pos hε)) ?_) (half_lt_self hε)
  intro i
  rw [sub_apply, truncate_apply]
  split_ifs with hi
  · simpa using le_of_lt (half_pos hε)
  · simpa using le_of_lt (hs i (fun his => hi (hst his)))

/-- For natural-indexed fibers, initial-segment truncations also converge. -/
theorem tendsto_truncate_range {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)]
    [∀ n, NormedSpace K (E n)] (x : DependentCZero K E) :
    Tendsto (fun N : ℕ => truncate (Finset.range N) x) atTop (𝓝 x) :=
  (tendsto_truncate x).comp tendsto_finset_range


/-- Coordinate vectors give an isometric copy of each fiber. -/
theorem isometry_single (i : I) : Isometry (single (K := K) (E := E) i) :=
  AddMonoidHomClass.isometry_of_norm (single (K := K) (E := E) i) (norm_single i)

/-- The defining submodule is closed in the ambient dependent ℓ∞ space. -/
theorem isClosed_submodule : IsClosed (dependentCZeroSubmodule K E : Set (lp E ∞)) :=
  (dependentCZeroSpan K E).isClosed_topologicalClosure

/-- Summary of the basic properties of `DependentCZero`: completeness, the
characterization by decay, the norm, coordinate maps, finite vectors and truncations. -/
theorem banach_sum [∀ i, CompleteSpace (E i)] :
    letI := Classical.decEq I
    CompleteSpace (DependentCZero K E) ∧
    IsClosed (dependentCZeroSubmodule K E : Set (lp E ∞)) ∧
    (∀ x : lp E ∞, x ∈ dependentCZeroSubmodule K E ↔
      Tendsto (fun i => ‖x i‖) cofinite (𝓝 0)) ∧
    (∀ x : DependentCZero K E,
      ‖x‖ = ⨆ i, ‖x i‖) ∧
    (∀ x : DependentCZero K E, ∀ i, ‖x i‖ ≤ ‖x‖) ∧
    (∀ x : DependentCZero K E, ∀ C : ℝ, 0 ≤ C → (∀ i, ‖x i‖ ≤ C) → ‖x‖ ≤ C) ∧
    (∀ i, ‖single (K := K) (E := E) i‖ ≤ 1 ∧
      ‖eval (K := K) (E := E) i‖ ≤ 1 ∧
      (eval (K := K) (E := E) i).comp (single i) = ContinuousLinearMap.id K (E i) ∧
      ∀ v : E i, ‖single (K := K) i v‖ = ‖v‖ ∧ single (K := K) i v i = v) ∧
    (∀ i j, i ≠ j → (eval (K := K) (E := E) i).comp (single j) = 0) ∧
    (∀ s : Finset I, ‖truncate (K := K) (E := E) s‖ ≤ 1 ∧
      ∀ x : DependentCZero K E, ∀ i,
        truncate s x i = if i ∈ s then x i else 0) ∧
    (∀ s : Finset I, ∀ v : ∀ i, E i,
      ‖finiteVector (K := K) s v‖₊ = s.sup (fun i => ‖v i‖₊)) ∧
    (∀ x : DependentCZero K E,
      Tendsto (fun s : Finset I => truncate s x) atTop (𝓝 x)) := by
  classical
  refine ⟨inferInstance, isClosed_submodule, mem_iff, norm_eq, norm_apply_le_norm,
    fun x C hC h => norm_le hC h, ?_, eval_comp_single_ne, ?_,
    nnnorm_finiteVector, tendsto_truncate⟩
  · exact fun i => ⟨norm_single_le i, norm_eval_le i, eval_comp_single i,
      fun v => ⟨norm_single i v, single_apply_self i v⟩⟩
  · exact fun s => ⟨norm_truncate_le s, truncate_apply s⟩

end DependentCZero

end Construction

namespace DependentCZero

section CoordinateSubspaces

variable {K : Type*} {I : Type*} {E : I → Type*}
  [NontriviallyNormedField K] [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace K (E i)]
variable (D : ∀ i, Submodule K (E i))

/-- The coordinatewise submodule of dependent `c₀` associated with `D`. -/
def coordinateSubmodule : Submodule K (DependentCZero K E) :=
  ⨅ i, (D i).comap (eval (K := K) (E := E) i).toLinearMap

@[simp]
theorem mem_coordinateSubmodule (x : DependentCZero K E) :
    x ∈ coordinateSubmodule D ↔ ∀ i, x i ∈ D i := by
  simp [coordinateSubmodule]

/-- Coordinatewise inclusion of dependent `c₀` sums is isometric. -/
def coordinateInclusion : DependentCZero K (fun i ↦ D i) →ₗᵢ[K] DependentCZero K E where
  toFun x :=
    ⟨⟨fun i ↦ (x i : E i), memℓp_infty ⟨‖x‖, by
        rintro _ ⟨i, rfl⟩
        exact norm_apply_le_norm x i⟩⟩,
      (mem_iff _).2 (by simpa using tendsto_norm x)⟩
  map_add' x y := by
    apply Subtype.ext
    apply lp.ext
    funext i
    rfl
  map_smul' a x := by
    apply Subtype.ext
    apply lp.ext
    funext i
    rfl
  norm_map' x := by
    rw [norm_eq, norm_eq]
    rfl

@[simp]
theorem coordinateInclusion_apply (x : DependentCZero K (fun i ↦ D i)) (i : I) :
    coordinateInclusion D x i = (x i : E i) := rfl

/-- Regard a vector whose coordinates lie in `D` as a vector in the dependent sum of `D`. -/
def coordinateRestriction (x : coordinateSubmodule D) : DependentCZero K (fun i ↦ D i) :=
  ⟨⟨fun i ↦ ⟨(x : DependentCZero K E) i, (mem_coordinateSubmodule D _).1 x.property i⟩,
      memℓp_infty ⟨‖(x : DependentCZero K E)‖, by
        rintro _ ⟨i, rfl⟩
        exact norm_apply_le_norm (x : DependentCZero K E) i⟩⟩,
    (mem_iff _).2 (by simpa using tendsto_norm (x : DependentCZero K E))⟩

@[simp]
theorem coordinateRestriction_apply (x : coordinateSubmodule D) (i : I) :
    (coordinateRestriction D x i : E i) = (x : DependentCZero K E) i := rfl

/-- The range of coordinate inclusion is precisely the coordinatewise submodule. -/
theorem range_coordinateInclusion :
    (coordinateInclusion D).toLinearMap.range = coordinateSubmodule D := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (mem_coordinateSubmodule D _).2 fun i ↦ (y i).property
  · intro hx
    refine ⟨coordinateRestriction D ⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    apply lp.ext
    funext i
    rfl

/-- The `c₀` sum of the subspaces `D i` is isometric to the coordinatewise submodule. -/
def coordinateEquiv :
    DependentCZero K (fun i ↦ D i) ≃ₗᵢ[K] coordinateSubmodule D where
  toFun x := ⟨coordinateInclusion D x,
    (mem_coordinateSubmodule D _).2 fun i ↦ (x i).property⟩
  invFun := coordinateRestriction D
  map_add' x y := by
    apply Subtype.ext
    exact map_add (coordinateInclusion D) x y
  map_smul' a x := by
    apply Subtype.ext
    exact map_smul (coordinateInclusion D) a x
  left_inv x := by
    apply Subtype.ext
    apply lp.ext
    funext i
    rfl
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply lp.ext
    funext i
    rfl
  norm_map' x := (coordinateInclusion D).norm_map x

@[simp]
theorem coordinateEquiv_apply (x : DependentCZero K (fun i ↦ D i)) :
    (coordinateEquiv D x : DependentCZero K E) = coordinateInclusion D x := rfl

@[simp]
theorem coordinateEquiv_symm_apply (x : coordinateSubmodule D) :
    (coordinateEquiv D).symm x = coordinateRestriction D x := rfl

/-- Closed coordinate subspaces define a closed subspace of dependent `c₀`. -/
theorem isClosed_coordinateSubmodule (hD : ∀ i, IsClosed (D i : Set (E i))) :
    IsClosed (coordinateSubmodule D : Set (DependentCZero K E)) := by
  change IsClosed ((⨅ i, (D i).comap (eval (K := K) (E := E) i).toLinearMap :
    Submodule K (DependentCZero K E)) : Set (DependentCZero K E))
  rw [Submodule.coe_iInf]
  exact isClosed_iInter fun i ↦ (hD i).preimage (eval (K := K) (E := E) i).continuous

theorem isClosed_range_coordinateInclusion (hD : ∀ i, IsClosed (D i : Set (E i))) :
    IsClosed (Set.range (coordinateInclusion D)) := by
  change IsClosed ((coordinateInclusion D).toLinearMap.range : Set (DependentCZero K E))
  rw [range_coordinateInclusion]
  exact isClosed_coordinateSubmodule D hD

/-- A closed coordinatewise subspace is Banach when the ambient fibers are Banach. -/
theorem completeSpace_coordinateSubmodule [∀ i, CompleteSpace (E i)]
    (hD : ∀ i, IsClosed (D i : Set (E i))) : CompleteSpace (coordinateSubmodule D) :=
  (isClosed_coordinateSubmodule D hD).completeSpace_coe

/-- The sum of closed coordinate subspaces is Banach when the ambient fibers are Banach. -/
theorem completeSpace_coordinateSum [∀ i, CompleteSpace (E i)]
    (hD : ∀ i, IsClosed (D i : Set (E i))) :
    CompleteSpace (DependentCZero K (fun i ↦ D i)) := by
  have : ∀ i, CompleteSpace (D i) := fun i ↦ (hD i).completeSpace_coe
  infer_instance

-- Direct instances on this nested subtype, to help instance search.
instance coordinateSubmoduleNormedAddCommGroup : NormedAddCommGroup (coordinateSubmodule D) :=
  inferInstance

instance coordinateSubmoduleNormedSpace : NormedSpace K (coordinateSubmodule D) :=
  inferInstance

/-- Projection from the concrete coordinate subspace onto one of its fibers. -/
def coordinateEval (i : I) : coordinateSubmodule D →L[K] D i :=
  ((eval (K := K) (E := E) i).comp (coordinateSubmodule D).subtypeL).codRestrict
    (D i) (fun x ↦ (mem_coordinateSubmodule D _).1 x.property i)

@[simp]
theorem coordinateEval_apply (i : I) (x : coordinateSubmodule D) :
    (coordinateEval D i x : E i) = (x : DependentCZero K E) i := rfl

theorem norm_coordinateEval_le (i : I) : ‖coordinateEval D i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul]
  exact norm_apply_le_norm (x : DependentCZero K E) i

/-- Summary of the coordinatewise subspace construction for closed subspaces `D i`. -/
theorem closed_coordinate_subspaces [∀ i, CompleteSpace (E i)]
    (hD : ∀ i, IsClosed (D i : Set (E i))) :
    (∀ x : DependentCZero K E, x ∈ coordinateSubmodule D ↔ ∀ i, x i ∈ D i) ∧
    (coordinateInclusion D).toLinearMap.range = coordinateSubmodule D ∧
    IsClosed (coordinateSubmodule D : Set (DependentCZero K E)) ∧
    IsClosed (Set.range (coordinateInclusion D)) ∧
    CompleteSpace (coordinateSubmodule D) ∧
    CompleteSpace (DependentCZero K (fun i ↦ D i)) ∧
    (∀ x : DependentCZero K (fun i ↦ D i),
      ‖coordinateInclusion D x‖ = ‖x‖ ∧
      (coordinateEquiv D x : DependentCZero K E) = coordinateInclusion D x ∧
      ∀ i, coordinateInclusion D x i = (x i : E i)) ∧
    (∀ i, ‖eval (K := K) (E := fun i ↦ D i) i‖ ≤ 1) ∧
    (∀ i, ‖coordinateEval D i‖ ≤ 1 ∧
      ∀ x : coordinateSubmodule D,
        (coordinateEval D i x : E i) = (x : DependentCZero K E) i) := by
  refine ⟨mem_coordinateSubmodule D, range_coordinateInclusion D,
    isClosed_coordinateSubmodule D hD, isClosed_range_coordinateInclusion D hD, completeSpace_coordinateSubmodule D hD,
    completeSpace_coordinateSum D hD, ?_, norm_eval_le, ?_⟩
  · exact fun x ↦ ⟨(coordinateInclusion D).norm_map x, rfl, fun _ ↦ rfl⟩
  · exact fun i ↦ ⟨norm_coordinateEval_le D i, fun _ ↦ rfl⟩

end CoordinateSubspaces

end DependentCZero

/- Geometric bounds for `ℕ`-indexed families. The convention starts in degree one:
the `n`-th coordinate is bounded by `C * r^(n+1)`. -/

namespace DependentCZero

section Geometric

variable {K : Type*} [NontriviallyNormedField K]
variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)]
variable [∀ n, NormedSpace K (E n)]

private lemma geometric_bound_le {C r : ℝ} (hC : 0 ≤ C) (hr₀ : 0 ≤ r)
    (hr₁ : r < 1) (n : ℕ) : C * r ^ (n + 1) ≤ C := by
  have hp : r ^ (n + 1) ≤ 1 := pow_le_one₀ hr₀ hr₁.le
  simpa using mul_le_mul_of_nonneg_left hp hC

private lemma geometric_memℓp (v : ∀ n, E n) {C r : ℝ} (hC : 0 ≤ C)
    (hr₀ : 0 ≤ r) (hr₁ : r < 1) (hv : ∀ n, ‖v n‖ ≤ C * r ^ (n + 1)) :
    Memℓp v ∞ := by
  apply memℓp_infty
  refine ⟨C, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact (hv n).trans (geometric_bound_le hC hr₀ hr₁ n)

/-- The bound for the coordinate convention starting in degree one tends to zero. -/
theorem tendsto_geometric_bound {C r : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r < 1) :
    Tendsto (fun n : ℕ => C * r ^ (n + 1)) atTop (𝓝 0) := by
  simpa only [mul_zero, Function.comp_def] using
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hr₀ hr₁).comp
      (tendsto_add_atTop_nat 1)).const_mul C

private lemma geometric_tendsto (v : ∀ n, E n) {C r : ℝ}
    (hr₀ : 0 ≤ r) (hr₁ : r < 1) (hv : ∀ n, ‖v n‖ ≤ C * r ^ (n + 1)) :
    Tendsto (fun n => ‖v n‖) cofinite (𝓝 0) := by
  rw [Nat.cofinite_eq_atTop]
  exact squeeze_zero (fun n => norm_nonneg _) hv (tendsto_geometric_bound hr₀ hr₁)

/-- A family with geometric coordinate bounds, as an element of c₀. -/
def ofGeometric (v : ∀ n, E n) {C r : ℝ} (hC : 0 ≤ C)
    (hr₀ : 0 ≤ r) (hr₁ : r < 1) (hv : ∀ n, ‖v n‖ ≤ C * r ^ (n + 1)) :
    DependentCZero K E :=
  ⟨⟨v, geometric_memℓp v hC hr₀ hr₁ hv⟩,
    (mem_iff _).2 (geometric_tendsto v hr₀ hr₁ hv)⟩

@[simp] theorem ofGeometric_apply (v : ∀ n, E n) {C r : ℝ} (hC : 0 ≤ C)
    (hr₀ : 0 ≤ r) (hr₁ : r < 1) (hv : ∀ n, ‖v n‖ ≤ C * r ^ (n + 1))
    (n : ℕ) : ofGeometric (K := K) v hC hr₀ hr₁ hv n = v n := rfl

/-- Under the bounds `‖x n‖ ≤ C * r^(n+1)`, truncation to the coordinates `n < N`
has error at most `C * r^(N+1)`. -/
theorem norm_sub_truncate_range_le (x : DependentCZero K E) {C r : ℝ}
    (hC : 0 ≤ C) (hr₀ : 0 ≤ r) (hr₁ : r < 1)
    (hx : ∀ n, ‖x n‖ ≤ C * r ^ (n + 1)) (N : ℕ) :
    ‖x - truncate (Finset.range N) x‖ ≤ C * r ^ (N + 1) := by
  apply norm_le (mul_nonneg hC (pow_nonneg hr₀ _))
  intro n
  by_cases hn : n < N
  · simpa [truncate_apply, Finset.mem_range, hn] using
      (mul_nonneg hC (pow_nonneg hr₀ (N + 1)))
  · have hNn : N + 1 ≤ n + 1 := Nat.add_le_add_right (Nat.le_of_not_gt hn) 1
    have hbound := (hx n).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr₀ hr₁.le hNn) hC)
    simpa [truncate_apply, Finset.mem_range, hn] using hbound

/-- Coordinates and truncation estimates for `ofGeometric`. -/
theorem geometric_construction (v : ∀ n, E n) {C r : ℝ} (hC : 0 ≤ C)
    (hr₀ : 0 ≤ r) (hr₁ : r < 1) (hv : ∀ n, ‖v n‖ ≤ C * r ^ (n + 1)) :
    (∀ n, ofGeometric (K := K) v hC hr₀ hr₁ hv n = v n) ∧
    (∀ N, ‖ofGeometric (K := K) v hC hr₀ hr₁ hv -
      truncate (Finset.range N) (ofGeometric (K := K) v hC hr₀ hr₁ hv)‖ ≤
        C * r ^ (N + 1)) ∧
    Tendsto (fun N => truncate (Finset.range N) (ofGeometric (K := K) v hC hr₀ hr₁ hv))
      atTop (𝓝 (ofGeometric (K := K) v hC hr₀ hr₁ hv)) := by
  refine ⟨fun _ => rfl, ?_, tendsto_truncate_range _⟩
  exact fun N => norm_sub_truncate_range_le _ hC hr₀ hr₁ hv N

/-- A common geometric coordinate bound gives uniform convergence on any set. -/
theorem tendstoUniformlyOn_truncate_range {X : Type*} (f : X → DependentCZero K E)
    (A : Set X) {C r : ℝ} (hC : 0 ≤ C) (hr₀ : 0 ≤ r) (hr₁ : r < 1)
    (hf : ∀ x ∈ A, ∀ n, ‖f x n‖ ≤ C * r ^ (n + 1)) :
    TendstoUniformlyOn (fun N x => truncate (Finset.range N) (f x)) f atTop A := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(tendsto_geometric_bound (C := C) hr₀ hr₁).eventually (gt_mem_nhds hε)]
    with N hN
  intro x hx
  rw [dist_eq_norm]
  exact (norm_sub_truncate_range_le (f x) hC hr₀ hr₁ (hf x hx) N).trans_lt hN

/-- Reconstruct a family from coordinate values on a set, extending by zero outside it. -/
noncomputable def ofGeometricOn {X : Type*} (v : X → ∀ n, E n) (A : Set X)
    {C r : ℝ} (hC : 0 ≤ C) (hr₀ : 0 ≤ r) (hr₁ : r < 1)
    (hv : ∀ x ∈ A, ∀ n, ‖v x n‖ ≤ C * r ^ (n + 1)) :
    X → DependentCZero K E := by
  classical
  exact fun x => if hx : x ∈ A then ofGeometric (v x) hC hr₀ hr₁ (hv x hx) else 0

@[simp] theorem ofGeometricOn_apply {X : Type*} (v : X → ∀ n, E n) (A : Set X)
    {C r : ℝ} (hC : 0 ≤ C) (hr₀ : 0 ≤ r) (hr₁ : r < 1)
    (hv : ∀ x ∈ A, ∀ n, ‖v x n‖ ≤ C * r ^ (n + 1)) (x : X) (hx : x ∈ A)
    (n : ℕ) : ofGeometricOn (K := K) v A hC hr₀ hr₁ hv x n = v x n := by
  classical
  simp [ofGeometricOn, hx]

/-- Coordinates and uniform truncation estimates for `ofGeometricOn` on `A`. -/
theorem geometric_uniform_construction {X : Type*} (v : X → ∀ n, E n) (A : Set X)
    {C r : ℝ} (hC : 0 ≤ C) (hr₀ : 0 ≤ r) (hr₁ : r < 1)
    (hv : ∀ x ∈ A, ∀ n, ‖v x n‖ ≤ C * r ^ (n + 1)) :
    (∀ x ∈ A, ∀ n, ofGeometricOn (K := K) v A hC hr₀ hr₁ hv x n = v x n) ∧
    (∀ N, ∀ x ∈ A, ‖ofGeometricOn (K := K) v A hC hr₀ hr₁ hv x -
      truncate (Finset.range N) (ofGeometricOn (K := K) v A hC hr₀ hr₁ hv x)‖ ≤
        C * r ^ (N + 1)) ∧
    TendstoUniformlyOn
      (fun N x => truncate (Finset.range N) (ofGeometricOn (K := K) v A hC hr₀ hr₁ hv x))
      (ofGeometricOn (K := K) v A hC hr₀ hr₁ hv) atTop A := by
  have hbound : ∀ x ∈ A, ∀ n,
      ‖ofGeometricOn (K := K) v A hC hr₀ hr₁ hv x n‖ ≤ C * r ^ (n + 1) := by
    intro x hx n
    simpa only [ofGeometricOn_apply v A hC hr₀ hr₁ hv x hx n] using hv x hx n
  exact ⟨fun x hx n => ofGeometricOn_apply v A hC hr₀ hr₁ hv x hx n,
    fun N x hx => norm_sub_truncate_range_le _ hC hr₀ hr₁ (hbound x hx) N,
    tendstoUniformlyOn_truncate_range _ A hC hr₀ hr₁ hbound⟩

end Geometric

end DependentCZero
