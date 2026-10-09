/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
import Mathlib.Analysis.Calculus.ContDiff.ContinuousAlternatingMap
import Mathlib.Analysis.Normed.Field.Ultra
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.Order.Zorn
import Mathlib.Topology.MetricSpace.Pseudo.Defs


/-!
# Spherically complete spaces

`SphericallyCompleteSpace F` says that every nonempty family of closed balls of `F`, any two of
which meet, has a point in common. The main result is Ingleton's extension theorem
(Theorem D.3), in the form with simultaneous bounds used in the proof of Theorem 4.2.
The file also shows that spaces of multilinear and alternating maps into an ultrametric space
are ultrametric, and that proper ultrametric spaces and complete discretely normed fields are
spherically complete.
-/

open Metric ContinuousMultilinearMap ContinuousAlternatingMap
open scoped ContDiff NNReal

/-- Every nonempty family of closed balls, any two of which meet, has a common point. -/
class SphericallyCompleteSpace (F : Type*) [PseudoMetricSpace F] : Prop where
  inter_nonempty : ∀ S : Set (F × ℝ), S.Nonempty →
    (∀ p ∈ S, ∀ q ∈ S, (closedBall p.1 p.2 ∩ closedBall q.1 q.2).Nonempty) →
    (⋂ p ∈ S, closedBall p.1 p.2).Nonempty


/-!
## The extension theorem

Let `S` be a nonempty family of pairs `(T_α, r_α)` of continuous linear maps `X → F` and radii
with `‖T_α - T_β‖ ≤ max r_α r_β`, and let `T₀` be a linear map on a submodule `D` with
`‖T₀ d - T_α d‖ ≤ r_α ‖d‖`. Then `T₀` extends to a continuous linear `T : X →L[𝕜] F` with
`‖T x - T_α x‖ ≤ r_α ‖x‖` for all `α`. Taking `S = {(0, 1)}` gives norm-preserving extension.
The proof is a Zorn's lemma argument on `X →ₗ.[𝕜] F`. Only `X` and `F` are assumed ultrametric.
-/

open Metric ContinuousMultilinearMap ContinuousAlternatingMap
open scoped ContDiff NNReal

section Master

variable {𝕜 X F : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup X] [NormedSpace 𝕜 X] [IsUltrametricDist X]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [IsUltrametricDist F] [SphericallyCompleteSpace F]

namespace MasterExtension

open Submodule

/-- The `S`-approximation property of a partially defined linear map. -/
def IsGood (S : Set ((X →L[𝕜] F) × ℝ)) (f : X →ₗ.[𝕜] F) : Prop :=
  ∀ p ∈ S, ∀ d : f.domain, ‖f d - p.1 d‖ ≤ p.2 * ‖(d : X)‖

omit [IsUltrametricDist F] [SphericallyCompleteSpace F] in
/-- Two closed balls whose centres are at distance at most the larger radius meet. -/
theorem balls_meet {c₁ c₂ : F} {r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁) (h₂ : 0 ≤ r₂)
    (h : dist c₁ c₂ ≤ max r₁ r₂) : (closedBall c₁ r₁ ∩ closedBall c₂ r₂).Nonempty := by
  rcases le_total r₁ r₂ with h' | h'
  · exact ⟨c₁, by simp [h₁], by simpa [max_eq_right h'] using h⟩
  · exact ⟨c₂, by simpa [dist_comm, max_eq_left h'] using h, by simp [h₂]⟩

variable {S : Set ((X →L[𝕜] F) × ℝ)}

omit [IsUltrametricDist X] [SphericallyCompleteSpace F] in
/-- The radii occurring in `S` are nonnegative. -/
theorem radius_nonneg (hS : ∀ p ∈ S, ∀ q ∈ S, ‖p.1 - q.1‖ ≤ max p.2 q.2) {p} (hp : p ∈ S) :
    0 ≤ p.2 := by
  have := hS p hp p hp
  simpa using this

omit [SphericallyCompleteSpace F] in
/-- The estimate between the centres of two of the balls, in the case `p.2 ≤ q.2`. -/
theorem centre_dist_aux (hS : ∀ p ∈ S, ∀ q ∈ S, ‖p.1 - q.1‖ ≤ max p.2 q.2)
    {f : X →ₗ.[𝕜] F} (hf : IsGood S f) (x : X)
    {p q : (X →L[𝕜] F) × ℝ} (hp : p ∈ S) (hq : q ∈ S) (hpq : p.2 ≤ q.2)
    (d e : f.domain) :
    ‖(p.1 ((d : X) + x) - f d) - (q.1 ((e : X) + x) - f e)‖
      ≤ max (p.2 * ‖(d : X) + x‖) (q.2 * ‖(e : X) + x‖) := by
  have hp0 : 0 ≤ p.2 := radius_nonneg hS hp
  have key : (p.1 ((d : X) + x) - f d) - (q.1 ((e : X) + x) - f e)
      = (p.1 ((d : X) - (e : X)) - f (d - e)) + ((p.1 - q.1) ((e : X) + x)) := by
    have hfde : f (d - e) = f d - f e := map_sub _ _ _
    have h1 : p.1 ((d : X) - (e : X)) = p.1 ((d : X) + x) - p.1 ((e : X) + x) := by
      rw [← map_sub]; congr 1; abel
    simp only [_root_.sub_apply, hfde, h1]
    abel
  rw [key]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · -- `‖(p.1 - f)(d - e)‖ ≤ p.2 * ‖d - e‖ ≤ p.2 * max ‖d+x‖ ‖e+x‖`
    have h1 : ‖f (d - e) - p.1 ((d : X) - (e : X))‖ ≤ p.2 * ‖(d : X) - (e : X)‖ := by
      have := hf p hp (d - e)
      simpa using this
    have h2 : ‖p.1 ((d : X) - (e : X)) - f (d - e)‖ ≤ p.2 * ‖(d : X) - (e : X)‖ := by
      rw [← norm_neg]; simpa using h1
    refine h2.trans ?_
    have h3 : ‖(d : X) - (e : X)‖ ≤ max ‖(d : X) + x‖ ‖(e : X) + x‖ := by
      have h := IsUltrametricDist.norm_add_le_max ((d : X) + x) (-((e : X) + x))
      rw [show ((d : X) + x) + (-((e : X) + x)) = (d : X) - (e : X) by abel, norm_neg] at h
      exact h
    calc p.2 * ‖(d : X) - (e : X)‖ ≤ p.2 * max ‖(d : X) + x‖ ‖(e : X) + x‖ := by
          exact mul_le_mul_of_nonneg_left h3 hp0
      _ = max (p.2 * ‖(d : X) + x‖) (p.2 * ‖(e : X) + x‖) := by
          rw [mul_max_of_nonneg _ _ hp0]
      _ ≤ max (p.2 * ‖(d : X) + x‖) (q.2 * ‖(e : X) + x‖) :=
          max_le_max le_rfl (mul_le_mul_of_nonneg_right hpq (norm_nonneg _))
  · refine (((p.1 - q.1).le_opNorm _).trans ?_).trans (le_max_right _ _)
    exact mul_le_mul_of_nonneg_right ((hS p hp q hq).trans (max_eq_right hpq).le)
      (norm_nonneg _)

/-- A good partial map with proper domain extends to a strictly larger good one. -/
theorem step (hne : S.Nonempty) (hS : ∀ p ∈ S, ∀ q ∈ S, ‖p.1 - q.1‖ ≤ max p.2 q.2)
    {f : X →ₗ.[𝕜] F} (hf : IsGood S f) (hdom : f.domain ≠ ⊤) :
    ∃ g, f < g ∧ IsGood S g := by
  obtain ⟨x, -, hx⟩ : ∃ x ∈ (⊤ : Submodule 𝕜 X), x ∉ f.domain :=
    SetLike.exists_of_lt (lt_top_iff_ne_top.2 hdom)
  -- the family of balls
  set B : Set (F × ℝ) :=
    {z | ∃ p ∈ S, ∃ d : f.domain, z = (p.1 ((d : X) + x) - f d, p.2 * ‖(d : X) + x‖)} with hB
  have hBne : B.Nonempty := by
    obtain ⟨p, hp⟩ := hne
    exact ⟨_, ⟨p, hp, 0, rfl⟩⟩
  have hBmeet : ∀ z ∈ B, ∀ w ∈ B, (closedBall z.1 z.2 ∩ closedBall w.1 w.2).Nonempty := by
    rintro z ⟨p, hp, d, rfl⟩ w ⟨q, hq, e, rfl⟩
    have hp0 : 0 ≤ p.2 := radius_nonneg hS hp
    have hq0 : 0 ≤ q.2 := radius_nonneg hS hq
    refine balls_meet (mul_nonneg hp0 (norm_nonneg _)) (mul_nonneg hq0 (norm_nonneg _)) ?_
    rw [dist_eq_norm]
    rcases le_total p.2 q.2 with h | h
    · exact centre_dist_aux hS hf x hp hq h d e
    · rw [← norm_neg, max_comm]
      simpa using centre_dist_aux hS hf x hq hp h e d
  obtain ⟨c, hc⟩ := SphericallyCompleteSpace.inter_nonempty B hBne hBmeet
  simp only [Set.mem_iInter] at hc
  have hc' : ∀ p ∈ S, ∀ d : f.domain,
      ‖(p.1 ((d : X) + x) - f d) - c‖ ≤ p.2 * ‖(d : X) + x‖ := by
    intro p hp d
    have := hc _ ⟨p, hp, d, rfl⟩
    rw [mem_closedBall, dist_eq_norm] at this
    rw [← norm_neg]
    simpa using this
  refine ⟨f.supSpanSingleton x c hx, ?_, ?_⟩
  · refine lt_iff_le_not_ge.2 ⟨f.left_le_sup _ _, fun H => ?_⟩
    replace H := LinearPMap.domain_mono.monotone H
    rw [LinearPMap.domain_supSpanSingleton, sup_le_iff, span_le, Set.singleton_subset_iff] at H
    exact hx H.2
  · rintro p hp ⟨z, hz⟩
    have hp0 : 0 ≤ p.2 := radius_nonneg hS hp
    rw [LinearPMap.domain_supSpanSingleton] at hz
    rcases mem_sup.1 hz with ⟨d, hd, y', hy', rfl⟩
    rcases mem_span_singleton.1 hy' with ⟨l, rfl⟩
    rw [LinearPMap.supSpanSingleton_apply_mk _ _ _ _ _ hd]
    rcases eq_or_ne l 0 with rfl | hl
    · simpa using hf p hp ⟨d, hd⟩
    · -- scale down by `l`
      have hde : (l⁻¹ • d) ∈ f.domain := f.domain.smul_mem _ hd
      have hball := hc' p hp ⟨l⁻¹ • d, hde⟩
      have hlne : ‖l‖ ≠ 0 := by simpa using hl
      have hl0 : (0:ℝ) < ‖l‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hlne)
      have hmul := mul_le_mul_of_nonneg_left hball (le_of_lt hl0)
      have e1 : l • (p.1 ((l⁻¹ • d : X) + x) - f ⟨l⁻¹ • d, hde⟩ - c)
          = -(f ⟨d, hd⟩ + l • c - p.1 (d + l • x)) := by
        have hfl : f ⟨l⁻¹ • d, hde⟩ = l⁻¹ • f ⟨d, hd⟩ := by
          have h : (⟨l⁻¹ • d, hde⟩ : f.domain) = l⁻¹ • (⟨d, hd⟩ : f.domain) := rfl
          rw [h]
          exact f.map_smul _ _
        rw [hfl]
        rw [smul_sub, smul_sub, ← map_smul, smul_add, smul_smul, mul_inv_cancel₀ hl,
          one_smul, smul_smul, mul_inv_cancel₀ hl, one_smul]
        abel
      have e2 : ‖l‖ * ‖(l⁻¹ • d : X) + x‖ = ‖d + l • x‖ := by
        rw [← norm_smul, smul_add, smul_smul, mul_inv_cancel₀ hl, one_smul]
      calc ‖f ⟨d, hd⟩ + l • c - p.1 (d + l • x)‖
          = ‖l • (p.1 ((l⁻¹ • d : X) + x) - f ⟨l⁻¹ • d, hde⟩ - c)‖ := by
            rw [e1, norm_neg]
        _ = ‖l‖ * ‖p.1 ((l⁻¹ • d : X) + x) - f ⟨l⁻¹ • d, hde⟩ - c‖ := by rw [norm_smul]
        _ ≤ ‖l‖ * (p.2 * ‖(l⁻¹ • d : X) + x‖) := hmul
        _ = p.2 * (‖l‖ * ‖(l⁻¹ • d : X) + x‖) := by ring
        _ = p.2 * ‖d + l • x‖ := by rw [e2]

/-- Every good partial map extends to a good map defined everywhere. -/
theorem exists_top (hne : S.Nonempty) (hS : ∀ p ∈ S, ∀ q ∈ S, ‖p.1 - q.1‖ ≤ max p.2 q.2)
    (f : X →ₗ.[𝕜] F) (hf : IsGood S f) :
    ∃ g ≥ f, g.domain = ⊤ ∧ IsGood S g := by
  have hSc : ∀ c, c ⊆ {g : X →ₗ.[𝕜] F | IsGood S g} → IsChain (· ≤ ·) c →
      ∀ y ∈ c, ∃ ub ∈ {g : X →ₗ.[𝕜] F | IsGood S g}, ∀ z ∈ c, z ≤ ub := by
    intro c hcs c_chain y hy
    have cne : c.Nonempty := ⟨y, hy⟩
    have hcd : DirectedOn (· ≤ ·) c := c_chain.directedOn
    refine ⟨LinearPMap.sSup c hcd, ?_, fun _ ↦ LinearPMap.le_sSup hcd⟩
    rintro p hp ⟨z, hz⟩
    have hdir : DirectedOn (· ≤ ·) (LinearPMap.domain '' c) :=
      directedOn_image.2 (hcd.mono LinearPMap.domain_mono.monotone)
    rcases (mem_sSup_of_directed (cne.image _) hdir).1 hz with ⟨_, ⟨g, hgc, rfl⟩, hgz⟩
    have hle : g ≤ LinearPMap.sSup c hcd := LinearPMap.le_sSup _ hgc
    have heq : (LinearPMap.sSup c hcd) ⟨z, hz⟩ = g ⟨z, hgz⟩ := (hle.2 rfl).symm
    rw [heq]
    exact hcs hgc p hp ⟨z, hgz⟩
  obtain ⟨q, hpq, hqs, hq⟩ := zorn_le_nonempty₀ {g : X →ₗ.[𝕜] F | IsGood S g} hSc f hf
  refine ⟨q, hpq, ?_, hqs⟩
  by_contra hdom
  obtain ⟨r, hqr, hr⟩ := step hne hS hqs hdom
  exact absurd (hq hr hqr.le) hqr.not_ge

end MasterExtension

open MasterExtension in
/-- Ingleton's extension theorem with simultaneous bounds (Theorem D.3). -/
theorem exists_extension_of_sphericallyComplete
    (S : Set ((X →L[𝕜] F) × ℝ)) (hne : S.Nonempty)
    (hS : ∀ p ∈ S, ∀ q ∈ S, ‖p.1 - q.1‖ ≤ max p.2 q.2)
    (D : Submodule 𝕜 X) (T₀ : D →ₗ[𝕜] F)
    (h₀ : ∀ p ∈ S, ∀ d : D, ‖T₀ d - p.1 d‖ ≤ p.2 * ‖(d : X)‖) :
    ∃ T : X →L[𝕜] F, (∀ d : D, T d = T₀ d) ∧ ∀ p ∈ S, ∀ x, ‖T x - p.1 x‖ ≤ p.2 * ‖x‖ := by
  obtain ⟨⟨g_dom, g⟩, ⟨-, hfg⟩, (rfl : g_dom = ⊤), hgs⟩ :=
    exists_top hne hS (⟨D, T₀⟩ : X →ₗ.[𝕜] F) (fun p hp d => h₀ p hp d)
  set G : X →ₗ[𝕜] F := g.comp (LinearMap.id.codRestrict ⊤ fun _ ↦ trivial) with hG
  obtain ⟨p₀, hp₀⟩ := hne
  have hGbound : ∀ x : X, ‖G x‖ ≤ max p₀.2 ‖p₀.1‖ * ‖x‖ := by
    intro x
    have h1 : ‖G x - p₀.1 x‖ ≤ p₀.2 * ‖x‖ := hgs p₀ hp₀ ⟨x, trivial⟩
    have h2 : ‖p₀.1 x‖ ≤ ‖p₀.1‖ * ‖x‖ := p₀.1.le_opNorm x
    have : G x = (G x - p₀.1 x) + p₀.1 x := by abel
    rw [this]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
    rw [max_mul_of_nonneg _ _ (norm_nonneg x)]
    exact max_le_max h1 h2
  refine ⟨G.mkContinuous _ hGbound, ?_, ?_⟩
  · intro d
    exact (hfg (rfl : ((d : X)) = ((⟨(d : X), trivial⟩ : (⊤ : Submodule 𝕜 X)) : X))).symm
  · intro p hp x
    exact hgs p hp ⟨x, trivial⟩

end Master


/-!
## Ultrametric spaces of multilinear and alternating maps

If `F` is ultrametric, so are `ContinuousMultilinearMap 𝕜 (fun _ : ι ↦ E) F` and
`E [⋀^ι]→L[𝕜] F` with their operator norms.
-/

open Metric ContinuousMultilinearMap ContinuousAlternatingMap
open scoped ContDiff NNReal

section Alt

variable {𝕜 ι E E' F : Type*} [NontriviallyNormedField 𝕜] [IsUltrametricDist 𝕜] [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [IsUltrametricDist F] [SphericallyCompleteSpace F]

instance : IsUltrametricDist (ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F) := by
  refine IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun f g => ?_
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m => ?_
  calc ‖(f + g) m‖ = ‖f m + g m‖ := by rw [_root_.add_apply]
    _ ≤ max ‖f m‖ ‖g m‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ max ‖f‖ ‖g‖ * ∏ i, ‖m i‖ := by
        rw [max_mul_of_nonneg _ _ (by positivity)]
        exact max_le_max (f.le_opNorm m) (g.le_opNorm m)

instance : IsUltrametricDist (E [⋀^ι]→L[𝕜] F) := by
  refine IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun f g => ?_
  have hfg : ‖f + g‖ = ‖(f + g).toContinuousMultilinearMap‖ := rfl
  rw [hfg, ContinuousAlternatingMap.toContinuousMultilinearMap_add]
  exact IsUltrametricDist.norm_add_le_max _ _

end Alt


/-!
## Proper ultrametric spaces are spherically complete

In an ultrametric space two closed balls are nested or disjoint, so a pairwise-meeting family of
closed balls is directed. In a proper space the balls are compact, so they have a common point.
-/

open Metric ContinuousMultilinearMap ContinuousAlternatingMap
open scoped ContDiff NNReal


/-- A proper ultrametric space is spherically complete. -/
instance {F : Type*} [PseudoMetricSpace F] [IsUltrametricDist F] [ProperSpace F] :
    SphericallyCompleteSpace F := by
  constructor
  intro S hne hS
  have : Nonempty S := hne.to_subtype
  have key : (⋂ p : S, closedBall (p : F × ℝ).1 (p : F × ℝ).2).Nonempty := by
    refine IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      (fun p : S => closedBall (p : F × ℝ).1 (p : F × ℝ).2) ?_ ?_ ?_ ?_
    · rintro ⟨p, hp⟩ ⟨q, hq⟩
      rcases IsUltrametricDist.closedBall_subset_trichotomy
        (x := p.1) (r := p.2) (y := q.1) (s := q.2) with h | h | h
      · exact ⟨⟨p, hp⟩, subset_rfl, h⟩
      · exact ⟨⟨q, hq⟩, h, subset_rfl⟩
      · exact absurd h (Set.not_disjoint_iff_nonempty_inter.mpr (hS p hp q hq))
    · rintro ⟨p, hp⟩
      exact (hS p hp p hp).mono Set.inter_subset_left
    · exact fun _ => isCompact_closedBall _ _
    · exact fun _ => isClosed_closedBall
  rwa [Set.biInter_eq_iInter]


/-!
## Complete discretely normed fields are spherically complete

If `K` is a complete ultrametric field whose nonzero norms are integer powers of a fixed
`e > 1`, then `K` is spherically complete. This does not use local compactness, so it applies
to fields such as `𝔽_p((X))`.
-/

open Metric ContinuousMultilinearMap ContinuousAlternatingMap
open scoped ContDiff NNReal

section DiscreteSphericallyComplete

open Filter Topology

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- A complete ultrametric field with norms in `e ^ ℤ ∪ {0}` is spherically complete. -/
theorem sphericallyCompleteSpace_of_discreteNorm {e : ℝ} (he : 1 < e)
    (hval : ∀ x : K, x ≠ 0 → ∃ n : ℤ, ‖x‖ = e ^ n) :
    SphericallyCompleteSpace K := by
  classical
  constructor
  intro S hSne hmeet
  -- radii are nonnegative
  have hrnn : ∀ p ∈ S, 0 ≤ p.2 := by
    intro p hp
    obtain ⟨z, hz, -⟩ := hmeet p hp p hp
    exact le_trans dist_nonneg (mem_closedBall.mp hz)
  -- centres are close
  have hdist : ∀ p ∈ S, ∀ q ∈ S, ‖p.1 - q.1‖ ≤ max p.2 q.2 := by
    intro p hp q hq
    obtain ⟨z, hz1, hz2⟩ := hmeet p hp q hq
    have h1 : ‖p.1 - z‖ ≤ p.2 := by
      rw [← dist_eq_norm, dist_comm]; exact mem_closedBall.mp hz1
    have h2 : ‖z - q.1‖ ≤ q.2 := by
      rw [← dist_eq_norm]; exact mem_closedBall.mp hz2
    calc ‖p.1 - q.1‖ = ‖(p.1 - z) + (z - q.1)‖ := by ring_nf
      _ ≤ max ‖p.1 - z‖ ‖z - q.1‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ max p.2 q.2 := max_le_max h1 h2
  by_cases hcase : ∃ p ∈ S, ∀ q ∈ S, ‖p.1 - q.1‖ ≤ q.2
  · obtain ⟨p, hp, h⟩ := hcase
    refine ⟨p.1, ?_⟩
    simp only [Set.mem_iInter]
    intro q hq
    rw [mem_closedBall, dist_eq_norm]
    exact h q hq
  · push Not at hcase
    -- one step of the descent
    have step : ∀ p : K × ℝ, p ∈ S → ∃ q, q ∈ S ∧ ‖p.1 - q.1‖ ≤ p.2 ∧ q.2 < ‖p.1 - q.1‖ := by
      intro p hp
      obtain ⟨q, hq, hlt⟩ := hcase p hp
      refine ⟨q, hq, ?_, hlt⟩
      have := hdist p hp q hq
      rcases max_cases p.2 q.2 with ⟨h, -⟩ | ⟨h, -⟩
      · rwa [h] at this
      · exact absurd (this.trans_eq h) (not_le.mpr hlt)
    choose! nxt hnxtS hnxt1 hnxt2 using step
    obtain ⟨p₀, hp₀⟩ := hSne
    set u : ℕ → K × ℝ := fun n => Nat.rec p₀ (fun _ q => nxt q) n with hu
    have huS : ∀ n, u n ∈ S := by
      intro n; induction n with
      | zero => exact hp₀
      | succ n ih => exact hnxtS _ ih
    set d : ℕ → ℝ := fun n => ‖(u n).1 - (u (n + 1)).1‖ with hd
    have hd_le : ∀ n, d n ≤ (u n).2 := fun n => hnxt1 _ (huS n)
    have hd_gt : ∀ n, (u (n + 1)).2 < d n := fun n => hnxt2 _ (huS n)
    have hd_pos : ∀ n, 0 < d n := fun n => lt_of_le_of_lt (hrnn _ (huS (n + 1))) (hd_gt n)
    have hd_anti : ∀ n, d (n + 1) < d n := fun n => lt_of_le_of_lt (hd_le (n + 1)) (hd_gt n)
    -- the discrete exponents
    have hd_mono : ∀ n m : ℕ, n ≤ m → d m ≤ d n := by
      intro n m h
      induction m with
      | zero => have hn : n = 0 := Nat.le_zero.mp h; subst hn; exact le_rfl
      | succ m ih =>
        rcases Nat.lt_or_ge n (m + 1) with hh | hh
        · exact le_trans (hd_anti m).le (ih (Nat.lt_succ_iff.mp hh))
        · have hn : n = m + 1 := le_antisymm h hh
          subst hn; exact le_rfl
    have hexp : ∀ n, ∃ k : ℤ, d n = e ^ k := by
      intro n
      refine hval _ (fun h0 => ?_)
      have hz : d n = 0 := by simp [hd, h0]
      exact absurd hz (hd_pos n).ne'
    choose k hk using hexp
    have hk_anti : ∀ n, k (n + 1) < k n := by
      intro n
      have := hd_anti n
      rw [hk (n + 1), hk n] at this
      exact (zpow_lt_zpow_iff_right₀ he).mp this
    have hk_le : ∀ n, k n ≤ k 0 - n := by
      intro n; induction n with
      | zero => simp
      | succ n ih =>
        have := hk_anti n
        push_cast
        omega
    have he0 : (0:ℝ) < e := lt_trans zero_lt_one he
    have hd_tendsto : Tendsto d atTop (𝓝 0) := by
      have hbound : ∀ n : ℕ, d n ≤ (e ^ (k 0)) * (e⁻¹) ^ n := by
        intro n
        rw [hk n]
        have : k n ≤ k 0 - n := hk_le n
        calc e ^ (k n) ≤ e ^ (k 0 - (n:ℤ)) := by
              exact zpow_le_zpow_right₀ he.le this
          _ = (e ^ (k 0)) * (e⁻¹) ^ n := by
              rw [zpow_sub₀ (ne_of_gt he0)]
              simp [zpow_natCast, inv_pow, div_eq_mul_inv]
      have h1 : Tendsto (fun n : ℕ => (e ^ (k 0)) * (e⁻¹) ^ n) atTop (𝓝 0) := by
        have : Tendsto (fun n : ℕ => (e⁻¹) ^ n) atTop (𝓝 0) :=
          tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
            (by rw [inv_lt_one₀ he0]; exact he)
        simpa using this.const_mul (e ^ (k 0))
      exact squeeze_zero (fun n => (hd_pos n).le) hbound h1
    -- the centres form a Cauchy sequence
    have hchain : ∀ n m : ℕ, n ≤ m → ‖(u n).1 - (u m).1‖ ≤ d n := by
      intro n m hnm
      induction m with
      | zero =>
        have hn : n = 0 := Nat.le_zero.mp hnm
        subst hn; simpa using (hd_pos 0).le
      | succ m ih =>
        rcases Nat.lt_or_ge n (m + 1) with h | h
        · have hnm' : n ≤ m := Nat.lt_succ_iff.mp h
          have h1 := ih hnm'
          have h2 : ‖(u m).1 - (u (m + 1)).1‖ = d m := rfl
          calc ‖(u n).1 - (u (m + 1)).1‖
              = ‖((u n).1 - (u m).1) + ((u m).1 - (u (m + 1)).1)‖ := by ring_nf
            _ ≤ max ‖(u n).1 - (u m).1‖ ‖(u m).1 - (u (m + 1)).1‖ :=
                IsUltrametricDist.norm_add_le_max _ _
            _ ≤ d n := max_le h1 (by rw [h2]; exact hd_mono n m hnm')
        · have hn : n = m + 1 := le_antisymm hnm h
          subst hn; simpa using (hd_pos (m + 1)).le
    have hcauchy : CauchySeq (fun n => (u n).1) := by
      refine cauchySeq_of_le_tendsto_0 d (fun n m N hn hm => ?_) hd_tendsto
      have h1 : ‖(u N).1 - (u n).1‖ ≤ d N := hchain N n hn
      have h2 : ‖(u N).1 - (u m).1‖ ≤ d N := hchain N m hm
      calc dist (u n).1 (u m).1 = ‖((u n).1 - (u N).1) + ((u N).1 - (u m).1)‖ := by
            rw [dist_eq_norm]; ring_nf
        _ ≤ max ‖(u n).1 - (u N).1‖ ‖(u N).1 - (u m).1‖ :=
            IsUltrametricDist.norm_add_le_max _ _
        _ ≤ d N := max_le (by rwa [← norm_neg, neg_sub]) h2
    obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcauchy
    refine ⟨x, ?_⟩
    simp only [Set.mem_iInter]
    intro q hq
    rw [mem_closedBall, dist_eq_norm]
    by_contra hcon
    push Not at hcon
    have hpos : 0 < ‖x - q.1‖ := lt_of_le_of_lt (hrnn q hq) hcon
    -- `‖x - u n‖ → 0`
    have ha : Tendsto (fun n => ‖x - (u n).1‖) atTop (𝓝 0) := by
      have h := tendsto_iff_dist_tendsto_zero.mp hx
      simpa [dist_eq_norm, norm_sub_rev] using h
    have hb : Tendsto (fun n => (u (n + 1)).2) atTop (𝓝 0) :=
      squeeze_zero (fun n => hrnn _ (huS (n + 1))) (fun n => (hd_gt n).le) hd_tendsto
    have hA : ∀ᶠ n in atTop, ‖x - (u n).1‖ < ‖x - q.1‖ := ha.eventually (eventually_lt_nhds hpos)
    have hB : ∀ᶠ n in atTop, (u (n + 1)).2 < ‖x - q.1‖ := hb.eventually (eventually_lt_nhds hpos)
    obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp hA
    obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.mp hB
    set j := max N1 N2 with hj
    have h1 : ‖x - (u (j + 1)).1‖ < ‖x - q.1‖ :=
      hN1 (j + 1) (le_trans (le_max_left N1 N2) (Nat.le_succ j))
    have h2 : (u (j + 1)).2 < ‖x - q.1‖ := hN2 j (le_max_right N1 N2)
    have h3 : ‖(u (j + 1)).1 - q.1‖ ≤ max ((u (j + 1)).2) q.2 :=
      hdist _ (huS (j + 1)) q hq
    have h4 : ‖x - q.1‖ ≤ max (‖x - (u (j + 1)).1‖) (‖(u (j + 1)).1 - q.1‖) := by
      calc ‖x - q.1‖ = ‖(x - (u (j + 1)).1) + ((u (j + 1)).1 - q.1)‖ := by ring_nf
        _ ≤ _ := IsUltrametricDist.norm_add_le_max _ _
    have h5 : max (‖x - (u (j + 1)).1‖) (‖(u (j + 1)).1 - q.1‖) < ‖x - q.1‖ :=
      max_lt h1 (lt_of_le_of_lt h3 (max_lt h2 hcon))
    exact absurd h4 (not_le.mpr h5)


end DiscreteSphericallyComplete
