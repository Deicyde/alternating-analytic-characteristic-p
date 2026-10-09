import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Support dimension of an exterior vector

The support dimension `sdim ω` is the least dimension of a finite-dimensional subspace whose
exterior power contains `ω` (Definition B.1). The minimum ranges over finite-dimensional
subspaces only, so the convention `finrank = 0` in infinite dimension does not interfere.
-/

namespace AlternatingAnalytic

open Module

variable {L : Type*} [Field L]
  {V : Type*} [AddCommGroup V] [Module L V] {k : ℕ}

/-- The exterior vectors supported by a subspace. -/
noncomputable def exteriorPowerSubmodule (k : ℕ) (W : Submodule L V) :
    Submodule L (⋀[L]^k V) :=
  LinearMap.range (exteriorPower.map k W.subtype)

/-- Enlarging the supporting subspace preserves support. -/
theorem exteriorPowerSubmodule_mono {U W : Submodule L V} (h : U ≤ W) :
    exteriorPowerSubmodule k U ≤ exteriorPowerSubmodule k W := by
  rintro _ ⟨a, rfl⟩
  refine ⟨exteriorPower.map k (Submodule.inclusion h) a, ?_⟩
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
  rfl

/-- A pure wedge is supported by any subspace containing its factors. -/
theorem ιMulti_mem_exteriorPowerSubmodule (W : Submodule L V) (x : Fin k → V)
    (hx : ∀ i, x i ∈ W) :
    exteriorPower.ιMulti L k x ∈ exteriorPowerSubmodule k W := by
  refine ⟨exteriorPower.ιMulti L k (fun i ↦ (⟨x i, hx i⟩ : W)), ?_⟩
  simp only [exteriorPower.map_apply_ιMulti]
  rfl

/-- Every exterior vector is supported on a finite-dimensional subspace. -/
theorem exists_finite_exterior_support (ω : ⋀[L]^k V) :
    ∃ W : Submodule L V, Module.Finite L W ∧ ω ∈ exteriorPowerSubmodule k W := by
  have hω : ω ∈ Submodule.span L (Set.range (exteriorPower.ιMulti L k)) := by
    rw [exteriorPower.ιMulti_span]
    exact Submodule.mem_top
  induction hω using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨x, rfl⟩ := h
    refine ⟨Submodule.span L (Set.range x),
      FiniteDimensional.span_of_finite L (Set.finite_range x), ?_⟩
    exact ιMulti_mem_exteriorPowerSubmodule _ x
      (fun i ↦ Submodule.subset_span (Set.mem_range_self i))
  | zero =>
    exact ⟨⊥, inferInstance, Submodule.zero_mem _⟩
  | add ω η _ _ hω hη =>
    obtain ⟨U, hU, hω⟩ := hω
    obtain ⟨W, hW, hη⟩ := hη
    let := hU
    let := hW
    refine ⟨U ⊔ W, inferInstance, ?_⟩
    exact Submodule.add_mem _ (exteriorPowerSubmodule_mono le_sup_left hω)
      (exteriorPowerSubmodule_mono le_sup_right hη)
  | smul c ω _ hω =>
    obtain ⟨W, hW, hω⟩ := hω
    exact ⟨W, hW, Submodule.smul_mem _ c hω⟩

/-- Some finite-dimensional subspace supports `ω`; used to define the minimum. -/
theorem exists_exterior_support_finrank (ω : ⋀[L]^k V) :
    ∃ n : ℕ, ∃ W : Submodule L V,
      Module.Finite L W ∧ ω ∈ exteriorPowerSubmodule k W ∧ finrank L W = n := by
  obtain ⟨W, hW, hω⟩ := exists_finite_exterior_support ω
  exact ⟨finrank L W, W, hW, hω, rfl⟩

/-- The minimum finite dimension of a subspace supporting an exterior vector. -/
noncomputable def exteriorSupportDim (ω : ⋀[L]^k V) : ℕ := by
  classical
  exact Nat.find (exists_exterior_support_finrank ω)

/-- A finite-dimensional supporting subspace attains the support dimension. -/
theorem exteriorSupportDim_attained (ω : ⋀[L]^k V) :
    ∃ W : Submodule L V, Module.Finite L W ∧
      ω ∈ exteriorPowerSubmodule k W ∧ finrank L W = exteriorSupportDim ω := by
  classical
  exact Nat.find_spec (exists_exterior_support_finrank ω)

/-- Every finite-dimensional supporting subspace bounds the support dimension. -/
theorem exteriorSupportDim_le_finrank (W : Submodule L V) [Module.Finite L W]
    {ω : ⋀[L]^k V} (hω : ω ∈ exteriorPowerSubmodule k W) :
    exteriorSupportDim ω ≤ finrank L W := by
  classical
  exact Nat.find_min' (exists_exterior_support_finrank ω) ⟨W, inferInstance, hω, rfl⟩

@[simp]
theorem exteriorSupportDim_zero : exteriorSupportDim (0 : ⋀[L]^k V) = 0 := by
  apply Nat.eq_zero_of_le_zero
  simpa using exteriorSupportDim_le_finrank (⊥ : Submodule L V) (Submodule.zero_mem _)

/-- Scalar multiplication does not increase support dimension. -/
theorem exteriorSupportDim_smul_le (c : L) (ω : ⋀[L]^k V) :
    exteriorSupportDim (c • ω) ≤ exteriorSupportDim ω := by
  obtain ⟨W, hW, hω, hdim⟩ := exteriorSupportDim_attained ω
  let := hW
  rw [← hdim]
  exact exteriorSupportDim_le_finrank W (Submodule.smul_mem _ c hω)

/-- Multiplication by a nonzero scalar preserves support dimension. -/
theorem exteriorSupportDim_smul (c : L) (hc : c ≠ 0) (ω : ⋀[L]^k V) :
    exteriorSupportDim (c • ω) = exteriorSupportDim ω := by
  apply le_antisymm (exteriorSupportDim_smul_le c ω)
  simpa only [inv_smul_smul₀ hc] using exteriorSupportDim_smul_le c⁻¹ (c • ω)

/-- Support dimension is subadditive. -/
theorem exteriorSupportDim_add_le (ω η : ⋀[L]^k V) :
    exteriorSupportDim (ω + η) ≤ exteriorSupportDim ω + exteriorSupportDim η := by
  obtain ⟨U, hU, hω, hdimω⟩ := exteriorSupportDim_attained ω
  obtain ⟨W, hW, hη, hdimη⟩ := exteriorSupportDim_attained η
  let := hU
  let := hW
  have hmem : ω + η ∈ exteriorPowerSubmodule k (U ⊔ W) :=
    Submodule.add_mem _ (exteriorPowerSubmodule_mono le_sup_left hω)
      (exteriorPowerSubmodule_mono le_sup_right hη)
  calc
    exteriorSupportDim (ω + η) ≤ finrank L (U ⊔ W : Submodule L V) :=
      exteriorSupportDim_le_finrank _ hmem
    _ ≤ finrank L U + finrank L W := Submodule.finrank_add_le_finrank_add_finrank U W
    _ = exteriorSupportDim ω + exteriorSupportDim η := by rw [hdimω, hdimη]

/-- A finite sum of wedges of vectors from a finite set is supported by its span. -/
theorem exteriorSupportDim_sum_wedges_le {ι : Type*} (s : Finset V) (t : Finset ι)
    (x : ι → Fin k → V) (hx : ∀ j ∈ t, ∀ i, x j i ∈ s) :
    exteriorSupportDim (∑ j ∈ t, exteriorPower.ιMulti L k (x j)) ≤
      finrank L (Submodule.span L (s : Set V)) := by
  apply exteriorSupportDim_le_finrank
  apply Submodule.sum_mem
  intro j hj
  exact ιMulti_mem_exteriorPowerSubmodule _ (x j)
    (fun i ↦ Submodule.subset_span (hx j hj i))

variable {V' : Type*} [AddCommGroup V'] [Module L V']

/-- A linear map carries supported exterior vectors to the image supporting subspace. -/
theorem exteriorPower_map_mem_exteriorPowerSubmodule (f : V →ₗ[L] V')
    (W : Submodule L V) {ω : ⋀[L]^k V} (hω : ω ∈ exteriorPowerSubmodule k W) :
    exteriorPower.map k f ω ∈ exteriorPowerSubmodule k (W.map f) := by
  obtain ⟨a, rfl⟩ := hω
  let g : W →ₗ[L] W.map f := (f.comp W.subtype).codRestrict (W.map f)
    (fun x ↦ Submodule.mem_map_of_mem x.property)
  refine ⟨exteriorPower.map k g a, ?_⟩
  change exteriorPower.map k (W.map f).subtype (exteriorPower.map k g a) =
    exteriorPower.map k f (exteriorPower.map k W.subtype a)
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp,
    ← LinearMap.comp_apply, ← exteriorPower.map_comp]
  rfl

/-- Support dimension does not increase under a linear map. -/
theorem exteriorSupportDim_map_le (f : V →ₗ[L] V') (ω : ⋀[L]^k V) :
    exteriorSupportDim (exteriorPower.map k f ω) ≤ exteriorSupportDim ω := by
  obtain ⟨W, hW, hω, hdim⟩ := exteriorSupportDim_attained ω
  let := hW
  calc
    exteriorSupportDim (exteriorPower.map k f ω) ≤ finrank L (W.map f) :=
      exteriorSupportDim_le_finrank _ (exteriorPower_map_mem_exteriorPowerSubmodule f W hω)
    _ ≤ finrank L W := Submodule.finrank_map_le f W
    _ = exteriorSupportDim ω := hdim

/-- The basic properties of support dimension listed after Definition B.1. -/
theorem exteriorSupportDim_properties (ι : Type*) :
    (∀ ω : ⋀[L]^k V, ∃ W : Submodule L V, Module.Finite L W ∧
      ω ∈ exteriorPowerSubmodule k W ∧ finrank L W = exteriorSupportDim ω) ∧
    exteriorSupportDim (0 : ⋀[L]^k V) = 0 ∧
    (∀ (c : L), c ≠ 0 → ∀ ω : ⋀[L]^k V,
      exteriorSupportDim (c • ω) = exteriorSupportDim ω) ∧
    (∀ ω η : ⋀[L]^k V,
      exteriorSupportDim (ω + η) ≤ exteriorSupportDim ω + exteriorSupportDim η) ∧
    (∀ (s : Finset V) (t : Finset ι) (x : ι → Fin k → V),
      (∀ j ∈ t, ∀ i, x j i ∈ s) →
      exteriorSupportDim (∑ j ∈ t, exteriorPower.ιMulti L k (x j)) ≤
        finrank L (Submodule.span L (s : Set V))) ∧
    (∀ (f : V →ₗ[L] V') (ω : ⋀[L]^k V),
      exteriorSupportDim (exteriorPower.map k f ω) ≤ exteriorSupportDim ω) := by
  exact ⟨exteriorSupportDim_attained, exteriorSupportDim_zero, exteriorSupportDim_smul,
    exteriorSupportDim_add_le, exteriorSupportDim_sum_wedges_le, exteriorSupportDim_map_le⟩

end AlternatingAnalytic
