/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
import AlternatingAnalytic.Analysis.SphericalCompleteness
import AlternatingAnalytic.Analysis.LiftCriterion
import Mathlib.Analysis.Calculus.ContDiff.ContinuousAlternatingMap
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

/-!
# Analytic precomposition with a spherically complete ultrametric target

Theorem 4.2. Over a nonarchimedean field, if `F` is ultrametric and spherically complete,
then `E [⋀^ι]→L[𝕜] F` is spherically complete and its inclusion into multilinear maps has a
retraction of norm at most one. Hence precomposition `f ↦ (m ↦ m ∘ f)` on alternating maps
is a continuous polynomial, in every characteristic and with no condition on `E` or `E'`.
The proof applies the extension theorem `exists_extension_of_sphericallyComplete` on the
free space `AltFree` of tuples.
-/

open Metric ContinuousMultilinearMap ContinuousAlternatingMap
open scoped ContDiff NNReal

noncomputable section

/-- The free `𝕜`-space on the set of `ι`-tuples of vectors of `E`, carrying the ultrametric
seminorm `‖f‖ = max_{v ∈ supp f} ‖f v‖ * ∏ i, ‖v i‖`. -/
def AltFree (𝕜 ι E : Type*) [NormedField 𝕜] [NormedAddCommGroup E] : Type _ :=
  (ι → E) →₀ 𝕜

namespace AltFree

variable {𝕜 ι E : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

instance : AddCommGroup (AltFree 𝕜 ι E) := inferInstanceAs (AddCommGroup ((ι → E) →₀ 𝕜))
instance : Module 𝕜 (AltFree 𝕜 ι E) := inferInstanceAs (Module 𝕜 ((ι → E) →₀ 𝕜))

/-- The identification of `AltFree` with `(ι → E) →₀ 𝕜`. -/
def toFin : AltFree 𝕜 ι E ≃ₗ[𝕜] ((ι → E) →₀ 𝕜) := LinearEquiv.refl 𝕜 _

/-- The weight `∏ i, ‖v i‖` of a tuple. -/
def wt (v : ι → E) : ℝ≥0 := ∏ i, ‖v i‖₊

/-- The `ℝ≥0`-valued seminorm on `AltFree`. -/
def nn (f : AltFree 𝕜 ι E) : ℝ≥0 :=
  (toFin f).support.sup fun v => ‖toFin f v‖₊ * wt v

instance : Norm (AltFree 𝕜 ι E) := ⟨fun f => nn f⟩

omit [NormedSpace 𝕜 E] in
lemma norm_def (f : AltFree 𝕜 ι E) : ‖f‖ = (nn f : ℝ) := rfl

omit [NormedSpace 𝕜 E] in
lemma le_nn (f : AltFree 𝕜 ι E) (v : ι → E) : ‖toFin f v‖₊ * wt v ≤ nn f := by
  by_cases hv : v ∈ (toFin f).support
  · exact Finset.le_sup (f := fun v => ‖toFin f v‖₊ * wt v) hv
  · simp only [Finsupp.mem_support_iff, not_not] at hv
    simp [hv]

omit [NormedSpace 𝕜 E] in
lemma nn_le {f : AltFree 𝕜 ι E} {C : ℝ≥0} (h : ∀ v, ‖toFin f v‖₊ * wt v ≤ C) : nn f ≤ C :=
  Finset.sup_le fun v _ => h v

omit [NormedSpace 𝕜 E] in
lemma nn_smul (c : 𝕜) (f : AltFree 𝕜 ι E) : nn (c • f) = ‖c‖₊ * nn f := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [nn]
  · have hsupp : (toFin (c • f)).support = (toFin f).support := by
      rw [map_smul]; exact Finsupp.support_smul_eq hc
    rw [nn, nn, hsupp, NNReal.mul_finset_sup]
    refine Finset.sup_congr rfl fun v _ => ?_
    rw [map_smul]
    simp [Finsupp.smul_apply, mul_assoc]

variable [IsUltrametricDist 𝕜]

omit [NormedSpace 𝕜 E] in
lemma nn_add_le (f g : AltFree 𝕜 ι E) : nn (f + g) ≤ max (nn f) (nn g) := by
  refine nn_le fun v => ?_
  have h1 : ‖toFin (f + g) v‖₊ ≤ max ‖toFin f v‖₊ ‖toFin g v‖₊ := by
    rw [map_add]
    exact IsUltrametricDist.nnnorm_add_le_max _ _
  calc ‖toFin (f + g) v‖₊ * wt v ≤ max ‖toFin f v‖₊ ‖toFin g v‖₊ * wt v := by gcongr
    _ = max (‖toFin f v‖₊ * wt v) (‖toFin g v‖₊ * wt v) := by
        rcases le_total ‖toFin f v‖₊ ‖toFin g v‖₊ with h | h
        · rw [max_eq_right h, max_eq_right (by gcongr)]
        · rw [max_eq_left h, max_eq_left (by gcongr)]
    _ ≤ max (nn f) (nn g) := max_le_max (le_nn f v) (le_nn g v)

omit [NormedSpace 𝕜 E] in
lemma core : SeminormedSpace.Core 𝕜 (AltFree 𝕜 ι E) where
  norm_nonneg x := (nn x).coe_nonneg
  norm_smul c x := by
    simp only [norm_def, nn_smul, NNReal.coe_mul, coe_nnnorm]
  norm_triangle x y := by
    have h : ((nn (x + y) : ℝ)) ≤ max (nn x : ℝ) (nn y : ℝ) := by exact_mod_cast nn_add_le x y
    simp only [norm_def]
    exact h.trans (max_le (le_add_of_nonneg_right (nn y).coe_nonneg)
      (le_add_of_nonneg_left (nn x).coe_nonneg))

instance : SeminormedAddCommGroup (AltFree 𝕜 ι E) := SeminormedAddCommGroup.ofCore core

instance : NormedSpace 𝕜 (AltFree 𝕜 ι E) := ⟨fun c x => (core.norm_smul c x).le⟩

instance : IsUltrametricDist (AltFree 𝕜 ι E) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y => by
    have h : ((nn (x + y) : ℝ)) ≤ max (nn x : ℝ) (nn y : ℝ) := by exact_mod_cast nn_add_le x y
    simpa only [norm_def] using h

/-- The basis element attached to a tuple. -/
def sng (v : ι → E) : AltFree 𝕜 ι E := toFin.symm (Finsupp.single v (1 : 𝕜))

omit [Fintype ι] [NormedSpace 𝕜 E] [IsUltrametricDist 𝕜] in
@[simp] lemma toFin_sng (v : ι → E) : toFin (sng v) = Finsupp.single v (1 : 𝕜) := rfl

omit [NormedSpace 𝕜 E] [IsUltrametricDist 𝕜] in
lemma nn_sng (v : ι → E) : nn (sng (𝕜 := 𝕜) v) = wt v := by
  classical
  rw [nn, toFin_sng, Finsupp.support_single _ (one_ne_zero)]
  simp

omit [NormedSpace 𝕜 E] [IsUltrametricDist 𝕜] in
lemma norm_sng (v : ι → E) : ‖sng (𝕜 := 𝕜) v‖ = ∏ i, ‖v i‖ := by
  rw [norm_def, nn_sng, wt]
  push_cast
  simp

section Hat

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [IsUltrametricDist F]

/-- The linear map on `AltFree` attached to a continuous multilinear map. -/
def hat (m : ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F) : AltFree 𝕜 ι E →ₗ[𝕜] F :=
  (Finsupp.linearCombination 𝕜 fun v : ι → E => m v).comp (toFin : _ ≃ₗ[𝕜] _).toLinearMap

omit [Fintype ι] [IsUltrametricDist 𝕜] [IsUltrametricDist F] in
lemma hat_apply (m : ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F) (f : AltFree 𝕜 ι E) :
    hat m f = (toFin f).sum fun v c => c • m v :=
  Finsupp.linearCombination_apply _ _

omit [Fintype ι] [IsUltrametricDist 𝕜] [IsUltrametricDist F] in
@[simp] lemma hat_sng (m : ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F) (v : ι → E) :
    hat m (sng v) = m v := by
  rw [hat, LinearMap.comp_apply]
  simp [Finsupp.linearCombination_single]

omit [IsUltrametricDist 𝕜] in
lemma hat_nnnorm_le (m : ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F) (f : AltFree 𝕜 ι E) :
    ‖hat m f‖₊ ≤ ‖m‖₊ * nn f := by
  rw [hat_apply, Finsupp.sum]
  refine IsUltrametricDist.nnnorm_sum_le_of_forall_le fun v _ => ?_
  rw [nnnorm_smul]
  calc ‖toFin f v‖₊ * ‖m v‖₊ ≤ ‖toFin f v‖₊ * (‖m‖₊ * wt v) := by
        gcongr; exact m.le_opNNNorm v
    _ = ‖m‖₊ * (‖toFin f v‖₊ * wt v) := by ring
    _ ≤ ‖m‖₊ * nn f := by gcongr; exact le_nn f v

omit [IsUltrametricDist 𝕜] in
lemma hat_norm_le (m : ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F) (f : AltFree 𝕜 ι E) :
    ‖hat m f‖ ≤ ‖m‖ * ‖f‖ := by
  exact_mod_cast hat_nnnorm_le m f

/-- The continuous linear map on `AltFree` attached to a continuous multilinear map. -/
def hatL (m : ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F) : AltFree 𝕜 ι E →L[𝕜] F :=
  (hat m).mkContinuous ‖m‖ (hat_norm_le m)

@[simp] lemma hatL_apply (m : ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F) (f : AltFree 𝕜 ι E) :
    hatL m f = hat m f := rfl

lemma hatL_norm_le (m : ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F) : ‖hatL m‖ ≤ ‖m‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

lemma hatL_sub (m m' : ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F) :
    hatL m - hatL m' = hatL (m - m') := by
  refine ContinuousLinearMap.ext fun f => ?_
  simp only [_root_.sub_apply, hatL_apply, hat_apply]
  rw [← Finsupp.sum_sub]
  exact Finsupp.sum_congr fun v _ => by simp [smul_sub]

end Hat

section Rels

variable (𝕜 ι E)

/-- The relations of multilinearity (additivity and homogeneity in one slot) and
alternation. They are stated without `Function.update`. -/
def rels : Set (AltFree 𝕜 ι E) :=
  {z | (∃ (v v' v'' : ι → E) (i : ι), (∀ j, j ≠ i → v j = v' j) ∧ (∀ j, j ≠ i → v j = v'' j) ∧
          v i = v' i + v'' i ∧ z = sng v - sng v' - sng v'') ∨
       (∃ (v v' : ι → E) (i : ι) (c : 𝕜), (∀ j, j ≠ i → v j = v' j) ∧ v i = c • v' i ∧
          z = sng v - c • sng v') ∨
       (∃ (v : ι → E) (i j : ι), i ≠ j ∧ v i = v j ∧ z = sng v)}

/-- The submodule of relations. -/
def relSub : Submodule 𝕜 (AltFree 𝕜 ι E) := Submodule.span 𝕜 (rels 𝕜 ι E)

variable {𝕜 ι E}

omit [Fintype ι] [IsUltrametricDist 𝕜] in
lemma sng_mem_relSub {v : ι → E} {i j : ι} (hij : i ≠ j) (hv : v i = v j) :
    sng (𝕜 := 𝕜) v ∈ relSub 𝕜 ι E :=
  Submodule.subset_span (Or.inr (Or.inr ⟨v, i, j, hij, hv, rfl⟩))

section Multilinear

variable {G : Type*} [AddCommGroup G] [Module 𝕜 G]

omit [Fintype ι] [IsUltrametricDist 𝕜] in
/-- Additivity in one slot, in the `update`-free formulation. -/
lemma _root_.MultilinearMap.add_of_agree (m : MultilinearMap 𝕜 (fun _ : ι => E) G)
    {v v' v'' : ι → E} {i : ι} (h' : ∀ j, j ≠ i → v j = v' j) (h'' : ∀ j, j ≠ i → v j = v'' j)
    (hi : v i = v' i + v'' i) : m v = m v' + m v'' := by
  classical
  have h1 : v = Function.update v' i (v' i + v'' i) := by
    funext j
    rcases eq_or_ne j i with rfl | hj
    · simpa using hi
    · simp [Function.update_of_ne hj, h' j hj]
  have h3 : Function.update v' i (v'' i) = v'' := by
    funext j
    rcases eq_or_ne j i with rfl | hj
    · simp
    · rw [Function.update_of_ne hj, ← h' j hj, h'' j hj]
  rw [h1, m.map_update_add, Function.update_eq_self, h3]

omit [Fintype ι] [IsUltrametricDist 𝕜] in
/-- Homogeneity in one slot, in the `update`-free formulation. -/
lemma _root_.MultilinearMap.smul_of_agree (m : MultilinearMap 𝕜 (fun _ : ι => E) G)
    {v v' : ι → E} {i : ι} {c : 𝕜} (h' : ∀ j, j ≠ i → v j = v' j) (hi : v i = c • v' i) :
    m v = c • m v' := by
  classical
  have h1 : v = Function.update v' i (c • v' i) := by
    funext j
    rcases eq_or_ne j i with rfl | hj
    · simpa using hi
    · simp [Function.update_of_ne hj, h' j hj]
  rw [h1, m.map_update_smul, Function.update_eq_self]

end Multilinear

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [IsUltrametricDist F]

omit [Fintype ι] [IsUltrametricDist 𝕜] [IsUltrametricDist F] in
/-- A continuous alternating map kills every relation. -/
lemma hat_eq_zero_of_mem_relSub (a : E [⋀^ι]→L[𝕜] F) :
    ∀ z ∈ relSub 𝕜 ι E, hat a.toContinuousMultilinearMap z = 0 := by
  have hgen : rels 𝕜 ι E ⊆ (LinearMap.ker (hat a.toContinuousMultilinearMap) : Set _) := by
    rintro z (⟨v, v', v'', i, h', h'', hi, rfl⟩ | ⟨v, v', i, c, h', hi, rfl⟩ |
      ⟨v, i, j, hij, hv, rfl⟩) <;>
      simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, hat_sng]
    · have h := a.toContinuousMultilinearMap.toMultilinearMap.add_of_agree h' h'' hi
      simp only [ContinuousMultilinearMap.coe_coe] at h
      rw [h]; abel
    · have h := a.toContinuousMultilinearMap.toMultilinearMap.smul_of_agree h' hi
      simp only [ContinuousMultilinearMap.coe_coe] at h
      rw [h]; abel
    · exact a.map_eq_zero_of_eq v hv hij
  intro z hz
  exact (Submodule.span_le.2 hgen) hz

/-- A continuous linear map on `AltFree` killing the relations is `v ↦ T (sng v)` for a unique
continuous alternating map. -/
def ofLinear (T : AltFree 𝕜 ι E →L[𝕜] F) (hT : ∀ z ∈ relSub 𝕜 ι E, T z = 0) :
    E [⋀^ι]→L[𝕜] F :=
  AlternatingMap.mkContinuous
    { toFun := fun v => T (sng v)
      map_update_add' := by
        intro _ v i x y
        have h := hT _ (Submodule.subset_span (Or.inl
          ⟨Function.update v i (x + y), Function.update v i x, Function.update v i y, i,
            fun j hj => by simp [Function.update_of_ne hj],
            fun j hj => by simp [Function.update_of_ne hj], by simp, rfl⟩))
        simp only [map_sub] at h
        rw [sub_sub, sub_eq_zero] at h
        exact h
      map_update_smul' := by
        intro _ v i c x
        have h := hT _ (Submodule.subset_span (Or.inr (Or.inl
          ⟨Function.update v i (c • x), Function.update v i x, i, c,
            fun j hj => by simp [Function.update_of_ne hj], by simp, rfl⟩)))
        simp only [map_sub, map_smul] at h
        rw [sub_eq_zero] at h
        exact h
      map_eq_zero_of_eq' := fun v i j hv hij => hT _ (sng_mem_relSub hij hv) }
    ‖T‖ fun v => by rw [← norm_sng (𝕜 := 𝕜) v]; exact T.le_opNorm _

omit [IsUltrametricDist F] in
@[simp] lemma ofLinear_apply (T : AltFree 𝕜 ι E →L[𝕜] F) (hT : ∀ z ∈ relSub 𝕜 ι E, T z = 0)
    (v : ι → E) : ofLinear T hT v = T (sng v) := rfl

end Rels

end AltFree

end -- noncomputable section

section Main

open AltFree

variable {𝕜 ι E F : Type*} [NontriviallyNormedField 𝕜] [IsUltrametricDist 𝕜] [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [IsUltrametricDist F] [SphericallyCompleteSpace F]

/-- Continuous alternating maps into a spherically complete ultrametric space form a
spherically complete space. -/
instance sphericallyCompleteSpace_continuousAlternatingMap :
    SphericallyCompleteSpace (E [⋀^ι]→L[𝕜] F) := by
  refine ⟨fun S hne hmeet => ?_⟩
  -- radii are nonnegative
  have hr : ∀ p ∈ S, 0 ≤ p.2 := fun p hp =>
    Metric.nonempty_closedBall.1 ((hmeet p hp p hp).mono Set.inter_subset_left)
  -- the centres are at distance at most the larger radius
  have hdist : ∀ p ∈ S, ∀ q ∈ S, ‖p.1 - q.1‖ ≤ max p.2 q.2 := by
    intro p hp q hq
    obtain ⟨a, ha, ha'⟩ := hmeet p hp q hq
    rw [← dist_eq_norm]
    refine (IsUltrametricDist.dist_triangle_max p.1 a q.1).trans (max_le_max ?_ ?_)
    · rw [dist_comm]; exact ha
    · exact ha'
  -- transport to continuous linear maps on `AltFree`
  set Φ : (E [⋀^ι]→L[𝕜] F) × ℝ → (AltFree 𝕜 ι E →L[𝕜] F) × ℝ :=
    fun p => (hatL p.1.toContinuousMultilinearMap, p.2) with hΦ
  have hS' : ∀ p ∈ Φ '' S, ∀ q ∈ Φ '' S, ‖p.1 - q.1‖ ≤ max p.2 q.2 := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    refine le_trans ?_ (hdist p hp q hq)
    rw [hΦ]
    simp only
    rw [hatL_sub]
    refine (hatL_norm_le _).trans_eq ?_
    rw [← ContinuousAlternatingMap.norm_toContinuousMultilinearMap (p.1 - q.1)]
    rfl
  have h0' : ∀ p ∈ Φ '' S, ∀ d : relSub 𝕜 ι E,
      ‖(0 : relSub 𝕜 ι E →ₗ[𝕜] F) d - p.1 d‖ ≤ p.2 * ‖(d : AltFree 𝕜 ι E)‖ := by
    rintro _ ⟨p, hp, rfl⟩ d
    have hd : hatL p.1.toContinuousMultilinearMap (d : AltFree 𝕜 ι E) = 0 :=
      hat_eq_zero_of_mem_relSub p.1 _ d.2
    simp only [LinearMap.zero_apply, hΦ, hd, sub_zero, norm_zero]
    have := hr p hp
    positivity
  obtain ⟨T, hT₀, hTS⟩ := exists_extension_of_sphericallyComplete (Φ '' S)
    (hne.image Φ) hS' (relSub 𝕜 ι E) 0 h0'
  · -- assemble the alternating map
    have hTrel : ∀ z ∈ relSub 𝕜 ι E, T z = 0 := fun z hz => by
      simpa using hT₀ ⟨z, hz⟩
    refine ⟨ofLinear T hTrel, ?_⟩
    simp only [Set.mem_iInter, Metric.mem_closedBall]
    intro p hp
    rw [dist_eq_norm]
    refine ContinuousAlternatingMap.opNorm_le_bound _ (hr p hp) fun v => ?_
    have := hTS (Φ p) ⟨p, hp, rfl⟩ (sng v)
    rw [norm_sng] at this
    simpa only [ContinuousAlternatingMap.sub_apply, ofLinear_apply, hΦ, hatL_apply, hat_sng,
      ContinuousAlternatingMap.coe_toContinuousMultilinearMap] using this

end Main

namespace ContinuousAlternatingMap

section Alt2

variable {𝕜 ι E E' F : Type*} [NontriviallyNormedField 𝕜] [IsUltrametricDist 𝕜] [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [IsUltrametricDist F] [SphericallyCompleteSpace F]

/-- The inclusion of alternating maps into multilinear maps has a retraction of norm at
most one. -/
theorem exists_contracting_retraction_toContinuousMultilinearMap :
    ∃ r : ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F →L[𝕜] (E [⋀^ι]→L[𝕜] F),
      ‖r‖ ≤ 1 ∧ ∀ a : E [⋀^ι]→L[𝕜] F, r a.toContinuousMultilinearMap = a := by
  classical
  set incl : (E [⋀^ι]→L[𝕜] F) →ₗ[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F :=
    ContinuousAlternatingMap.toContinuousMultilinearMapLinear with hincl
  have hinj : Function.Injective incl :=
    ContinuousAlternatingMap.toContinuousMultilinearMap_injective
  set T₀ : (LinearMap.range incl) →ₗ[𝕜] (E [⋀^ι]→L[𝕜] F) :=
    (LinearEquiv.ofInjective incl hinj).symm.toLinearMap with hT₀
  have key : ∀ d : LinearMap.range incl, incl (T₀ d) = (d : _) :=
    fun d => LinearEquiv.ofInjective_symm_apply (f := incl) (h := hinj) d
  -- the singleton family of balls: the zero map with radius `1`
  set S : Set ((ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F →L[𝕜] (E [⋀^ι]→L[𝕜] F)) × ℝ) :=
    {(0, 1)} with hS_def
  have hS : ∀ p ∈ S, ∀ q ∈ S, ‖p.1 - q.1‖ ≤ max p.2 q.2 := by
    rintro p rfl q rfl
    simp only [sub_self, max_self]
    exact le_trans (le_of_eq ContinuousLinearMap.opNorm_zero) zero_le_one
  have h₀ : ∀ p ∈ S, ∀ d : LinearMap.range incl,
      ‖T₀ d - p.1 d‖ ≤ p.2 * ‖(d : ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F)‖ := by
    rintro p rfl d
    have h1 : ‖(d : ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F)‖ = ‖T₀ d‖ := by
      rw [← key d]
      exact ContinuousAlternatingMap.norm_toContinuousMultilinearMap (T₀ d)
    simp only [zero_apply, sub_zero, one_mul, h1, le_refl]
  obtain ⟨T, hT, hbound⟩ :=
    exists_extension_of_sphericallyComplete (𝕜 := 𝕜)
      (X := ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F) (F := E [⋀^ι]→L[𝕜] F)
      S ⟨(0, 1), rfl⟩ hS (LinearMap.range incl) T₀ h₀
  have hnorm : ‖T‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simpa only [zero_apply, sub_zero, one_mul] using
      hbound (0, 1) (by rfl) x
  refine ⟨T, hnorm, fun a => ?_⟩
  have hmem : a.toContinuousMultilinearMap ∈ LinearMap.range incl := ⟨a, rfl⟩
  have := hT ⟨a.toContinuousMultilinearMap, hmem⟩
  exact this.trans (hinj (key ⟨a.toContinuousMultilinearMap, hmem⟩))

/-- A continuous linear retraction of the inclusion of alternating maps into multilinear maps. -/
theorem exists_retraction_toContinuousMultilinearMap :
    ∃ r : ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F →L[𝕜] (E [⋀^ι]→L[𝕜] F),
      ∀ a : E [⋀^ι]→L[𝕜] F, r a.toContinuousMultilinearMap = a := by
  obtain ⟨r, _, hr⟩ := exists_contracting_retraction_toContinuousMultilinearMap
    (𝕜 := 𝕜) (ι := ι) (E := E) (F := F)
  exact ⟨r, hr⟩

end Alt2

end ContinuousAlternatingMap

namespace ContinuousAlternatingMap

section TheoremA

variable {𝕜 ι E E' F : Type*} [NontriviallyNormedField 𝕜] [IsUltrametricDist 𝕜] [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [IsUltrametricDist F] [SphericallyCompleteSpace F]

omit [IsUltrametricDist 𝕜] [SphericallyCompleteSpace F] in
/-- If the inclusion of alternating maps into multilinear maps has a continuous linear
retraction, precomposition is `C^n` for every `n : WithTop ℕ∞`. -/
theorem contDiff_compContinuousLinearMapCLM_of_retraction {n : WithTop ℕ∞}
    (r : ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F →L[𝕜] (E [⋀^ι]→L[𝕜] F))
    (hr : ∀ a : E [⋀^ι]→L[𝕜] F, r a.toContinuousMultilinearMap = a) :
    ContDiff 𝕜 n (compContinuousLinearMapCLM :
      (E →L[𝕜] E') → (E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)) := by
  have hamb : ContDiff 𝕜 n fun f : E →L[𝕜] E' ↦
      (compContinuousLinearMapL (F := F) fun _ : ι ↦ f).comp (toContinuousMultilinearMapCLM 𝕜) :=
    ((compContinuousLinearMapContinuousMultilinear 𝕜 (fun _ : ι ↦ E) (fun _ ↦ E') F).contDiff.comp
      (contDiff_pi.2 fun _ ↦ contDiff_id)).clm_comp contDiff_const
  have := (contDiff_const (c := r) (𝕜 := 𝕜) (n := n) (E := E →L[𝕜] E')).clm_comp hamb
  convert this using 2 with f
  refine ContinuousLinearMap.ext fun m => ?_
  exact (hr (m.compContinuousLinearMap f)).symm

/-- Theorem 4.2: if `F` is ultrametric and spherically complete, precomposition on
alternating maps is `C^n` for every `n : WithTop ℕ∞`, in particular analytic. -/
theorem contDiff_compContinuousLinearMapCLM_of_sphericallyComplete {n : WithTop ℕ∞} :
    ContDiff 𝕜 n (compContinuousLinearMapCLM :
      (E →L[𝕜] E') → (E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)) := by
  obtain ⟨r, hr⟩ := exists_retraction_toContinuousMultilinearMap (𝕜 := 𝕜) (ι := ι) (E := E) (F := F)
  exact contDiff_compContinuousLinearMapCLM_of_retraction r hr

/-- Precomposition has a bounded multilinear lift. -/
theorem hasBoundedLift_of_sphericallyComplete :
    LiftCriterion.HasBoundedLift 𝕜 ι E E' F :=
  LiftCriterion.contDiff_omega_iff_hasBoundedLift.mp
    contDiff_compContinuousLinearMapCLM_of_sphericallyComplete

/-- Precomposition is a continuous polynomial at every point. -/
theorem cpolynomialAt_compContinuousLinearMapCLM_of_sphericallyComplete
    (f₀ : E →L[𝕜] E') :
    CPolynomialAt 𝕜 (compContinuousLinearMapCLM :
      (E →L[𝕜] E') → (E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)) f₀ := by
  obtain ⟨P, hP⟩ := hasBoundedLift_of_sphericallyComplete
    (𝕜 := 𝕜) (ι := ι) (E := E) (E' := E') (F := F)
  exact LiftCriterion.cpolynomialAt_of_lift P hP f₀

/-- Precomposition is analytic at every point. -/
theorem analyticAt_compContinuousLinearMapCLM_of_sphericallyComplete
    (f₀ : E →L[𝕜] E') :
    AnalyticAt 𝕜 (compContinuousLinearMapCLM :
      (E →L[𝕜] E') → (E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)) f₀ :=
  (cpolynomialAt_compContinuousLinearMapCLM_of_sphericallyComplete f₀).analyticAt

end TheoremA

end ContinuousAlternatingMap
