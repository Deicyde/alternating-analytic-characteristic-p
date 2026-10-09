import Mathlib.Analysis.Normed.Operator.LinearIsometry
import AlternatingAnalytic.Analysis.DenseScalarFamilyExtension
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# The dense source `E = K^I + K a`

For `K ⊆ L` and `a : I → L`, the `K`-subspace `E = K^I + K a` of `L^I` with the supremum norm.
If `a` is algebraically independent, `E` has dimension `card I + 1`, and it is dense when `K` is
dense in `L`. This is the space `E` of Lemma H.5.
-/

noncomputable section

open scoped NNReal

namespace AlternatingAnalytic.RigidDenseSource

section Algebra
variable (K L I : Type*) [Field K] [Field L] [Algebra K L]

/-- The coordinatewise scalar inclusion. -/
def coordinateMap : (I → K) →ₗ[K] (I → L) where
  toFun b i := algebraMap K L (b i)
  map_add' b c := by ext i; simp
  map_smul' s b := by ext i; simp [Algebra.smul_def]

@[simp] theorem coordinateMap_apply (b : I → K) (i : I) :
    coordinateMap K L I b i = algebraMap K L (b i) := rfl

variable {L I} (a : I → L)

/-- The `K`-subspace `K^I + K a` of `L^I`. -/
def source : Submodule K (I → L) :=
  LinearMap.range (coordinateMap K L I) ⊔ K ∙ a

theorem mem_source {x : I → L} : x ∈ source K a ↔
    ∃ b : I → K, ∃ s : K, ∀ i,
      x i = algebraMap K L (b i) + algebraMap K L s * a i := by
  constructor
  · intro hx
    obtain ⟨y, ⟨b, rfl⟩, z, hz, h⟩ := Submodule.mem_sup.mp hx
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hz
    exact ⟨b, s, fun i => by simpa [Algebra.smul_def] using (congrFun h i).symm⟩
  · rintro ⟨b, s, hx⟩
    apply Submodule.mem_sup.mpr
    refine ⟨coordinateMap K L I b, ⟨b, rfl⟩, s • a,
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a), ?_⟩
    ext i
    simpa [Algebra.smul_def] using (hx i).symm

theorem coordinateMap_mem (b : I → K) : coordinateMap K L I b ∈ source K a :=
  Submodule.mem_sup_left ⟨b, rfl⟩

/-- The generator `a` as an element of the source. -/
def generator : source K a :=
  ⟨a, Submodule.mem_sup_right (Submodule.mem_span_singleton_self a)⟩

theorem generator_mem : a ∈ source K a := (generator K a).property

@[simp] theorem coe_generator : (generator K a : I → L) = a := rfl

variable [DecidableEq I]

/-- The standard vector `e_i` as an element of the source. -/
def standard (i : I) : source K a :=
  ⟨Pi.single i 1, by
    apply (mem_source K a).mpr
    refine ⟨Pi.single i 1, 0, ?_⟩
    intro j
    by_cases h : j = i <;> simp [h]⟩

theorem standard_mem (i : I) : (Pi.single i 1 : I → L) ∈ source K a :=
  (standard K a i).property

@[simp] theorem coe_standard (i : I) : (standard K a i : I → L) = Pi.single i 1 := rfl

omit [DecidableEq I] in
instance nontrivial_source [Nonempty I] : Nontrivial (source K a) := by
  obtain ⟨i⟩ := ‹Nonempty I›
  let x : source K a := ⟨coordinateMap K L I (fun _ => 1),
    coordinateMap_mem K a (fun _ => 1)⟩
  refine ⟨⟨x, 0, ?_⟩⟩
  intro h
  have := congrArg (fun y : source K a => (y : I → L) i) h
  simp [x] at this

/-- The parametrization `(b, s) ↦ b + s a`, used to compute the dimension. -/
def representation : ((I → K) × K) →ₗ[K] (I → L) :=
  (coordinateMap K L I).comp (LinearMap.fst K (I → K) K) +
    (LinearMap.toSpanSingleton K (I → L) a).comp (LinearMap.snd K (I → K) K)

omit [DecidableEq I] in
@[simp] theorem representation_apply (b : I → K) (s : K) (i : I) :
    representation K a (b, s) i = algebraMap K L (b i) + algebraMap K L s * a i := by
  simp [representation, Algebra.smul_def]

omit [DecidableEq I] in
theorem range_representation : LinearMap.range (representation K a) = source K a := by
  ext x
  constructor
  · rintro ⟨⟨b, s⟩, rfl⟩
    exact (mem_source K a).mpr ⟨b, s, fun i => representation_apply K a b s i⟩
  · intro hx
    obtain ⟨b, s, h⟩ := (mem_source K a).mp hx
    exact ⟨(b, s), funext fun i => (representation_apply K a b s i).trans (h i).symm⟩

omit [DecidableEq I] in
theorem representation_injective [Nonempty I] (ha : AlgebraicIndependent K a) :
    Function.Injective (representation K a) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  rintro ⟨b, s⟩ h
  have hs : s = 0 := by
    by_contra hs
    obtain ⟨i⟩ := ‹Nonempty I›
    have hi := congrFun h i
    simp only [representation_apply, Pi.zero_apply] at hi
    have hsi : algebraMap K L s ≠ 0 := (map_ne_zero (algebraMap K L)).mpr hs
    have hai : a i = algebraMap K L (-(b i) / s) := by
      rw [map_div₀, map_neg]
      apply (eq_div_iff hsi).mpr
      exact (mul_comm _ _).trans (eq_neg_of_add_eq_zero_right hi)
    exact ha.transcendental i (hai ▸ isAlgebraic_algebraMap (-(b i) / s))
  subst s
  have hb : b = 0 := by
    ext i
    have hi := congrFun h i
    simpa using hi
  simp [hb]

variable [Fintype I] [Nonempty I]

omit [DecidableEq I] in
theorem finrank_source (ha : AlgebraicIndependent K a) :
    Module.finrank K (source K a) = Fintype.card I + 1 := by
  rw [← range_representation K a,
    LinearMap.finrank_range_of_inj (representation_injective K a ha)]
  simp [Module.finrank_prod]

omit [DecidableEq I] [Nonempty I] in
instance finiteDimensional_source :
    Module.Finite K (source K a) := by
  rw [← range_representation K a]
  infer_instance

end Algebra

section Norm
variable (K : Type*) {L I : Type*} [NontriviallyNormedField K]
  [NontriviallyNormedField L] [NormedAlgebra K L] [Fintype I] [DecidableEq I]
  (a : I → L)

@[simp] theorem norm_standard (i : I) : ‖standard K a i‖ = 1 := by
  change ‖(Pi.single i 1 : I → L)‖ = 1
  rw [Pi.norm_single, norm_one]

omit [DecidableEq I] in
/-- The source carries the supremum norm of `L^I`. -/
theorem norm_source (x : source K a) :
    ‖x‖ = (Finset.univ.sup fun i : I => ‖(x : I → L) i‖₊ : ℝ≥0) := rfl

variable {K a}

omit [DecidableEq I] in
theorem denseRange_subtype (hKL : DenseRange (algebraMap K L)) :
    DenseRange (source K a).subtypeₗᵢ := by
  have hd : DenseRange (coordinateMap K L I) := DenseRange.piMap fun _ => hKL
  apply hd.mono
  rintro _ ⟨b, rfl⟩
  exact ⟨⟨coordinateMap K L I b, coordinateMap_mem K a b⟩, rfl⟩

end Norm
end AlternatingAnalytic.RigidDenseSource
