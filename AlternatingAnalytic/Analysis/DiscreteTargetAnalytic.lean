/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
import AlternatingAnalytic.Analysis.DiscreteNormRounding
import AlternatingAnalytic.Analysis.DiscreteSphericalCompleteness
import AlternatingAnalytic.Analysis.SphericalAnalytic
import Mathlib.Algebra.Module.ULift
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-!
# Analytic precomposition for equivalent ultrametric targets over a discrete base

This is proposition `discrete` of `sources/charp.tex`. We construct the rounded norm on an
actual copy of the target, prove the identity is a continuous linear equivalence, transfer
completeness, and apply spherical completeness for discrete distances and Theorem A.
The given norm on the original target need not itself be ultrametric or discrete.
-/

open scoped ContDiff

namespace AlternatingAnalytic

/-- A separate carrier for the rounded target norm, with the same algebraic vector space. -/
def DiscreteRenormedTarget (F : Type*) := F

namespace DiscreteRenormedTarget

instance {F : Type*} [AddCommGroup F] : AddCommGroup (DiscreteRenormedTarget F) :=
  inferInstanceAs (AddCommGroup F)

instance {K F : Type*} [Semiring K] [AddCommGroup F] [Module K F] :
    Module K (DiscreteRenormedTarget F) := inferInstanceAs (Module K F)

/-- The algebraic identity from the separate normed carrier to the original space. -/
def linearEquiv (K F : Type*) [Semiring K] [AddCommGroup F] [Module K F] :
    DiscreteRenormedTarget F ≃ₗ[K] F := LinearEquiv.refl K F

end DiscreteRenormedTarget

/-- Equality with the nontrivial discrete value group supplies Mathlib's nontrivial norm
hypothesis; the underlying normed-field structure is unchanged. -/
@[instance_reducible]
def nontriviallyNormedFieldOfDiscreteValueGroup (K : Type*) [NormedField K]
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hvalue : Set.range (fun c : Kˣ => ‖(c : K)‖) = Set.range (fun n : ℤ => r ^ n)) :
    NontriviallyNormedField K where
  toNormedField := inferInstance
  non_trivial := by
    have hmem : r ^ (-1 : ℤ) ∈ Set.range (fun c : Kˣ => ‖(c : K)‖) := by
      rw [hvalue]
      exact ⟨-1, rfl⟩
    obtain ⟨c, hc⟩ := hmem
    refine ⟨(c : K), ?_⟩
    change ‖(c : K)‖ = r ^ (-1 : ℤ) at hc
    rw [hc, zpow_neg_one]
    exact (one_lt_inv₀ hr0).mpr hr1

/-- The value-group equality in the paper implies the containment used by the rounding proof. -/
theorem norm_mem_zpowers_of_discreteValueGroup {K : Type*} [NormedField K] {r : ℝ}
    (hvalue : Set.range (fun c : Kˣ => ‖(c : K)‖) = Set.range (fun n : ℤ => r ^ n))
    (c : K) (hc : c ≠ 0) : ∃ n : ℤ, ‖c‖ = r ^ n := by
  have hmem : ‖c‖ ∈ Set.range (fun d : Kˣ => ‖(d : K)‖) := ⟨Units.mk0 c hc, rfl⟩
  rw [hvalue] at hmem
  obtain ⟨n, hn⟩ := hmem
  exact ⟨n, hn.symm⟩

variable {K ι E E' F : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace K E] [NormedAddCommGroup E'] [NormedSpace K E']
  [NormedAddCommGroup F] [NormedSpace K F] [CompleteSpace F]

/-- A complete target with an equivalent ultrametric norm has bounded precomposition lifts
when the nonzero scalar norms lie in a discrete cyclic group. -/
theorem hasBoundedLift_of_equivalentUltrametricNorm_discreteField
    (hF : HasEquivalentUltrametricNorm K F) {e : ℝ} (he : 1 < e)
    (hval : ∀ c : K, c ≠ 0 → ∃ n : ℤ, ‖c‖ = e ^ n) :
    Round24Transfer.HasBoundedLift K ι E E' F := by
  obtain ⟨q, hq, ⟨A, hA, hlower⟩, ⟨B, hB, hupper⟩, hqval⟩ :=
    hF.exists_discrete he hval
  let G := DiscreteRenormedTarget F
  let : Norm G := ⟨fun x => q x⟩
  let core : NormedSpace.Core K G := {
    norm_nonneg := fun x => apply_nonneg q x
    norm_smul := fun c x => map_smul_eq_mul q c x
    norm_triangle := fun x y => map_add_le_add q x y
    norm_eq_zero_iff := fun x => by
      change q x = 0 ↔ x = 0
      constructor
      · intro hx
        exact norm_le_zero_iff.mp (by simpa only [hx, mul_zero] using hlower x)
      · intro hx
        subst x
        exact map_zero q }
  let : NormedAddCommGroup G := NormedAddCommGroup.ofCore core
  let : NormedSpace K G := NormedSpace.ofCore core
  let φ : G ≃ₗ[K] F := DiscreteRenormedTarget.linearEquiv K F
  let ψ : G ≃L[K] F := φ.toContinuousLinearEquivOfBounds A B
    (fun x => hlower x) (fun x => hupper x)
  let : CompleteSpace G :=
    (ψ.isUniformEmbedding.isUniformInducing.completeSpace_congr ψ.surjective).mpr inferInstance
  let : IsUltrametricDist G :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
      (fun x y => hq x y)
  let : SphericallyCompleteSpace G := by
    apply sphericallyCompleteSpace_of_discreteDist he
    intro x y hxy
    rw [dist_eq_norm]
    change ∃ n : ℤ, q (x - y) = e ^ n
    exact hqval _ (sub_ne_zero.mpr (fun hh => hxy hh))
  have hG : Round24Transfer.HasBoundedLift K ι E E' G :=
    ContinuousAlternatingMap.hasBoundedLift_of_sphericallyComplete
  exact Round24Transfer.hasBoundedLift_of_retract ψ.symm.toContinuousLinearMap
    ψ.toContinuousLinearMap (fun x => ψ.apply_symm_apply x) hG

/-- Under the discrete-base hypotheses, precomposition is continuously polynomial everywhere. -/
theorem cpolynomialAt_of_equivalentUltrametricNorm_discreteField
    (hF : HasEquivalentUltrametricNorm K F) {e : ℝ} (he : 1 < e)
    (hval : ∀ c : K, c ≠ 0 → ∃ n : ℤ, ‖c‖ = e ^ n) (f₀ : E →L[K] E') :
    CPolynomialAt K (Round24Transfer.Q K ι E E' F) f₀ := by
  obtain ⟨P, hP⟩ := hasBoundedLift_of_equivalentUltrametricNorm_discreteField
    (ι := ι) (E := E) (E' := E') hF he hval
  exact Round24Transfer.cpolynomialAt_of_lift P hP f₀

/-- The full discrete-base positive complement, for the original target norm. -/
theorem analyticAt_of_equivalentUltrametricNorm_discreteField
    (hF : HasEquivalentUltrametricNorm K F) {e : ℝ} (he : 1 < e)
    (hval : ∀ c : K, c ≠ 0 → ∃ n : ℤ, ‖c‖ = e ^ n) (f₀ : E →L[K] E') :
    AnalyticAt K (Round24Transfer.Q K ι E E' F) f₀ :=
  (cpolynomialAt_of_equivalentUltrametricNorm_discreteField hF he hval f₀).analyticAt

/-- The paper's radius convention, using powers of `r ∈ (0,1)`. -/
theorem cpolynomialAt_of_equivalentUltrametricNorm_discreteField_radius
    (hF : HasEquivalentUltrametricNorm K F) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hval : ∀ c : K, c ≠ 0 → ∃ n : ℤ, ‖c‖ = r ^ n) (f₀ : E →L[K] E') :
    CPolynomialAt K (Round24Transfer.Q K ι E E' F) f₀ := by
  apply cpolynomialAt_of_equivalentUltrametricNorm_discreteField hF
    ((one_lt_inv₀ hr0).mpr hr1) ?_ f₀
  intro c hc
  obtain ⟨n, hn⟩ := hval c hc
  exact ⟨-n, by simpa [zpow_neg] using hn⟩

/-- Analyticity everywhere in the paper's radius convention. -/
theorem analyticAt_of_equivalentUltrametricNorm_discreteField_radius
    (hF : HasEquivalentUltrametricNorm K F) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hval : ∀ c : K, c ≠ 0 → ∃ n : ℤ, ‖c‖ = r ^ n) (f₀ : E →L[K] E') :
    AnalyticAt K (Round24Transfer.Q K ι E E' F) f₀ :=
  (cpolynomialAt_of_equivalentUltrametricNorm_discreteField_radius hF hr0 hr1 hval f₀).analyticAt

/-- The paper's exact value-group hypothesis gives continuous polynomiality everywhere. -/
theorem cpolynomialAt_of_equivalentUltrametricNorm_discreteValueGroup
    (hF : HasEquivalentUltrametricNorm K F) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hvalue : Set.range (fun c : Kˣ => ‖(c : K)‖) = Set.range (fun n : ℤ => r ^ n))
    (f₀ : E →L[K] E') : CPolynomialAt K (Round24Transfer.Q K ι E E' F) f₀ :=
  cpolynomialAt_of_equivalentUltrametricNorm_discreteField_radius hF hr0 hr1
    (norm_mem_zpowers_of_discreteValueGroup hvalue) f₀

/-- Proposition `discrete`: analyticity for equivalent ultrametric Banach targets over a
field with value group `r^ℤ`, in the original target norm and without completeness of K. -/
theorem analyticAt_of_equivalentUltrametricNorm_discreteValueGroup
    (hF : HasEquivalentUltrametricNorm K F) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hvalue : Set.range (fun c : Kˣ => ‖(c : K)‖) = Set.range (fun n : ℤ => r ^ n))
    (f₀ : E →L[K] E') : AnalyticAt K (Round24Transfer.Q K ι E E' F) f₀ :=
  (cpolynomialAt_of_equivalentUltrametricNorm_discreteValueGroup hF hr0 hr1 hvalue f₀).analyticAt

end AlternatingAnalytic
