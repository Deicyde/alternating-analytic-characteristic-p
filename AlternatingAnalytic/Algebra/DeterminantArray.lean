import AlternatingAnalytic.Algebra.ExteriorSupportDimension
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Determinant arrays of exterior vectors

For a subspace `W` of the functions `S → L`, evaluating an exterior vector of `Λ^k W`
on `k`-tuples of points gives the determinant array Ω, and Ω is injective over any
field (Lemma B.2). The proof reduces to a finite-dimensional support, where the
coordinate evaluations span the dual.
-/

namespace AlternatingAnalytic

open Module

variable {L : Type*} [Field L]
  {V : Type*} [AddCommGroup V] [Module L V] {S : Type*} {k : ℕ}

/-- The array obtained by pairing an exterior vector with tuples of a family of linear forms. -/
noncomputable def exteriorEvaluationArray (e : S → Dual L V) :
    (⋀[L]^k V) →ₗ[L] ((Fin k → S) → L) :=
  LinearMap.pi fun c ↦ exteriorPower.alternatingMapToDual L V k (e ∘ c)

/-- On a pure wedge, evaluation is the determinant with evaluation points indexing rows. -/
theorem exteriorEvaluationArray_ιMulti (e : S → Dual L V) (x : Fin k → V)
    (c : Fin k → S) :
    exteriorEvaluationArray e (exteriorPower.ιMulti L k x) c =
      Matrix.det (fun i j ↦ e (c i) (x j)) := by
  simp only [exteriorEvaluationArray, LinearMap.pi_apply,
    exteriorPower.alternatingMapToDual_apply_ιMulti, Function.comp_apply]
  exact Matrix.det_transpose _

/-- Repeating an evaluation point makes the determinant array vanish. -/
theorem exteriorEvaluationArray_eq_zero_of_eq (e : S → Dual L V)
    (ω : ⋀[L]^k V) (c : Fin k → S) {i j : Fin k}
    (h : c i = c j) (hij : i ≠ j) : exteriorEvaluationArray e ω c = 0 := by
  have hzero := (exteriorPower.alternatingMapToDual L V k).map_eq_zero_of_eq
    (e ∘ c) (congrArg e h) hij
  exact congrArg (fun f : Dual L (⋀[L]^k V) ↦ f ω) hzero

/-- Permuting evaluation points multiplies the array by the permutation sign. -/
theorem exteriorEvaluationArray_perm (e : S → Dual L V) (ω : ⋀[L]^k V)
    (c : Fin k → S) (σ : Equiv.Perm (Fin k)) :
    exteriorEvaluationArray e ω (c ∘ σ) =
      Equiv.Perm.sign σ • exteriorEvaluationArray e ω c := by
  have hperm := (exteriorPower.alternatingMapToDual L V k).map_perm (e ∘ c) σ
  exact congrArg (fun f : Dual L (⋀[L]^k V) ↦ f ω) hperm

/-- Evaluation arrays commute with applying a linear map to exterior vectors. -/
theorem exteriorEvaluationArray_map {V' : Type*} [AddCommGroup V'] [Module L V']
    (e : S → Dual L V') (f : V →ₗ[L] V') (ω : ⋀[L]^k V) :
    exteriorEvaluationArray e (exteriorPower.map k f ω) =
      exteriorEvaluationArray (fun s ↦ (e s).comp f) ω := by
  have hmaps : (exteriorEvaluationArray e).comp (exteriorPower.map k f) =
      exteriorEvaluationArray (fun s ↦ (e s).comp f) := by
    apply exteriorPower.linearMap_ext
    ext x c
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      exteriorPower.map_apply_ιMulti, exteriorEvaluationArray_ιMulti, Function.comp_apply]
  exact LinearMap.congr_fun hmaps ω

/-- A spanning family of linear forms detects every exterior vector. -/
theorem exteriorEvaluationArray_injective_of_span_eq_top (e : S → Dual L V)
    (he : Submodule.span L (Set.range e) = ⊤) :
    Function.Injective (exteriorEvaluationArray (k := k) e) := by
  classical
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro ω hω
  let h : (⋀[L]^k (Dual L V)) →ₗ[L] L := (exteriorPower.pairingDual L V k).flip ω
  have hh : h = 0 := by
    apply LinearMap.ext_on (exteriorPower.ιMulti_span_of_span L k (Dual L V) he)
    rintro _ ⟨a, ha, rfl⟩
    have hex : ∀ i, ∃ s, e s = a i := fun i ↦ ha (Set.mem_range_self i)
    choose c hc using hex
    have htuple : e ∘ c = a := funext hc
    have hz := congrFun hω c
    simpa only [h, LinearMap.flip_apply, exteriorPower.pairingDual,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, exteriorEvaluationArray,
      LinearMap.pi_apply, htuple, Pi.zero_apply, LinearMap.zero_apply] using hz
  let : LinearOrder (Module.Free.ChooseBasisIndex L V) := linearOrderOfSTO WellOrderingRel
  let b := Module.Free.chooseBasis L V
  apply (b.exteriorPower k).ext_elem
  intro s
  simpa only [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual, map_zero,
    h, LinearMap.flip_apply, LinearMap.zero_apply, Finsupp.zero_apply] using
    LinearMap.congr_fun hh (exteriorPower.ιMulti_family L k b.coord s)

/-- Coordinate evaluations span the dual of every finite-dimensional function subspace. -/
theorem span_coordinate_evaluations (W : Submodule L (S → L)) [Module.Finite L W] :
    Submodule.span L (Set.range (fun s ↦ (LinearMap.proj s).comp W.subtype)) = ⊤ := by
  apply Submodule.span_eq_top_of_ne_zero
  intro z hz
  have hex : ∃ s, (z : S → L) s ≠ 0 := by
    by_contra! h
    apply hz
    apply Subtype.ext
    exact funext h
  obtain ⟨s, hs⟩ := hex
  exact ⟨_, Set.mem_range_self s, hs⟩

/-- The determinant array of an exterior vector of scalar functions. -/
noncomputable def determinantArray :
    (⋀[L]^k (S → L)) →ₗ[L] ((Fin k → S) → L) :=
  exteriorEvaluationArray (fun s ↦ LinearMap.proj s)

/-- The determinant array evaluates a pure wedge as a matrix determinant. -/
theorem determinantArray_ιMulti (x : Fin k → S → L) (c : Fin k → S) :
    determinantArray (exteriorPower.ιMulti L k x) c =
      Matrix.det (fun i j ↦ x j (c i)) :=
  exteriorEvaluationArray_ιMulti _ x c

/-- The determinant array is injective. -/
theorem determinantArray_injective :
    Function.Injective (determinantArray (L := L) (S := S) (k := k)) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro ω hω
  obtain ⟨W, hW, η, hη⟩ := exists_finite_exterior_support ω
  let := hW
  have hzero : exteriorEvaluationArray (fun s ↦ (LinearMap.proj s).comp W.subtype) η = 0 := by
    rw [← exteriorEvaluationArray_map, hη]
    exact hω
  have hηzero : η = 0 :=
    exteriorEvaluationArray_injective_of_span_eq_top _ (span_coordinate_evaluations W)
      (hzero.trans (map_zero _).symm)
  rw [← hη, hηzero, map_zero]

/-- The determinant array on an arbitrary subspace of scalar functions. -/
noncomputable def determinantArraySubmodule (W : Submodule L (S → L)) :
    (⋀[L]^k W) →ₗ[L] ((Fin k → S) → L) :=
  determinantArray.comp (exteriorPower.map k W.subtype)

/-- The determinant formula for an exterior vector of an arbitrary function subspace. -/
theorem determinantArraySubmodule_ιMulti (W : Submodule L (S → L))
    (x : Fin k → W) (c : Fin k → S) :
    determinantArraySubmodule W (exteriorPower.ιMulti L k x) c =
      Matrix.det (fun i j ↦ (x j : S → L) (c i)) := by
  simp only [determinantArraySubmodule, LinearMap.comp_apply,
    exteriorPower.map_apply_ιMulti, determinantArray_ιMulti, Function.comp_apply]
  rfl

/-- Lemma B.2: the determinant array on `Λ^k W` is injective. -/
theorem determinantArraySubmodule_injective (W : Submodule L (S → L)) :
    Function.Injective (determinantArraySubmodule (k := k) W) :=
  determinantArray_injective.comp
    (exteriorPower.map_injective_field (Submodule.subtype_injective W))

/-- An array vanishes when two of its evaluation coordinates coincide. -/
theorem determinantArraySubmodule_eq_zero_of_eq (W : Submodule L (S → L))
    (ω : ⋀[L]^k W) (c : Fin k → S) {i j : Fin k}
    (h : c i = c j) (hij : i ≠ j) : determinantArraySubmodule W ω c = 0 :=
  exteriorEvaluationArray_eq_zero_of_eq _ _ c h hij

/-- Permuting the coordinates of a determinant array introduces the permutation sign. -/
theorem determinantArraySubmodule_perm (W : Submodule L (S → L))
    (ω : ⋀[L]^k W) (c : Fin k → S) (σ : Equiv.Perm (Fin k)) :
    determinantArraySubmodule W ω (c ∘ σ) =
      Equiv.Perm.sign σ • determinantArraySubmodule W ω c :=
  exteriorEvaluationArray_perm _ _ c σ

/-- The determinant formula, injectivity and alternation of the determinant array. -/
theorem determinantArray_properties (W : Submodule L (S → L)) :
    (∀ (x : Fin k → W) (c : Fin k → S),
      determinantArraySubmodule W (exteriorPower.ιMulti L k x) c =
        Matrix.det (fun i j ↦ (x j : S → L) (c i))) ∧
    Function.Injective (determinantArraySubmodule (k := k) W) ∧
    (∀ (ω : ⋀[L]^k W) (c : Fin k → S) (i j : Fin k),
      c i = c j → i ≠ j → determinantArraySubmodule W ω c = 0) ∧
    (∀ (ω : ⋀[L]^k W) (c : Fin k → S) (σ : Equiv.Perm (Fin k)),
      determinantArraySubmodule W ω (c ∘ σ) =
        Equiv.Perm.sign σ • determinantArraySubmodule W ω c) := by
  exact ⟨determinantArraySubmodule_ιMulti W, determinantArraySubmodule_injective W,
    fun ω c _ _ ↦ determinantArraySubmodule_eq_zero_of_eq W ω c,
    determinantArraySubmodule_perm W⟩

end AlternatingAnalytic
