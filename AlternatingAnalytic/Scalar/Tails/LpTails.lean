import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Basic.Denumerable
import AlternatingAnalytic.Scalar.Tails.Multilinear
import AlternatingAnalytic.Scalar.Tails.NestedBalls

/-!
# Multilinear tails on `ℓ^∞(I, K)` (Lemma F.2)

Let `K` be complete, nonarchimedean and not spherically complete, and let `I` be countably
infinite. Transporting `tail_multilinear` from `ℓ^∞(ℕ, K)` along an enumeration of `I`, every
continuous `d`-linear form `μ` on `ℓ^∞(I, K)` has the tail property (`multilinear_tail`). As
consequences, the diagonal values `μ (e_i, …, e_i)` tend to `0` along the cofinite filter
(`multilinear_diagonal_tendsto_zero`) and the coefficient array `μ (e_{i_1}, …, e_{i_d})` is null
on `I^d` (`multilinear_coeff_tendsto_zero`). The expansion (F.1) is in `Tails/Expansion.lean`.
-/

namespace AlternatingAnalytic.Tails

open Filter Topology BoundedContinuousFunction
open scoped ENNReal

variable {K : Type*} [NontriviallyNormedField K] {I : Type*}

/-! ### Transport between `ℓ^∞(ℕ)` and `ℓ^∞(I)` -/

/-- Pull a bounded sequence back to `ℓ^∞(I)` along `e : I → ℕ`. -/
noncomputable def lpOfLinf (e : I → ℕ) : Linf K →L[K] lp (fun _ : I => K) ∞ :=
  LinearMap.mkContinuous
    { toFun := fun u => ⟨fun i => u (e i), memℓp_infty_iff.2
        ⟨‖u‖, by rintro _ ⟨i, rfl⟩; exact u.norm_coe_le_norm _⟩⟩
      map_add' := fun _ _ => lp.ext rfl
      map_smul' := fun _ _ => lp.ext rfl }
    1 (fun u => by
      rw [one_mul]
      exact lp.norm_le_of_forall_le (norm_nonneg u) fun i => u.norm_coe_le_norm _)

lemma lpOfLinf_apply (e : I → ℕ) (u : Linf K) (i : I) : lpOfLinf e u i = u (e i) := rfl

/-- Push a vector of `ℓ^∞(I)` to `ℓ^∞(ℕ)` along `e : ℕ → I`. -/
noncomputable def linfOfLp (e : ℕ → I) (x : lp (fun _ : I => K) ∞) : Linf K :=
  ofNormedAddCommGroupDiscrete (fun n => x (e n)) ‖x‖
    (fun _ => lp.norm_apply_le_norm ENNReal.top_ne_zero x _)

lemma linfOfLp_apply (e : ℕ → I) (x : lp (fun _ : I => K) ∞) (n : ℕ) :
    linfOfLp e x n = x (e n) := rfl

lemma norm_linfOfLp_le (e : ℕ → I) (x : lp (fun _ : I => K) ∞) : ‖linfOfLp e x‖ ≤ ‖x‖ :=
  (BoundedContinuousFunction.norm_le (norm_nonneg x)).2
    fun _ => lp.norm_apply_le_norm ENNReal.top_ne_zero x _

lemma lpOfLinf_linfOfLp (e : I ≃ ℕ) (x : lp (fun _ : I => K) ∞) :
    lpOfLinf e (linfOfLp e.symm x) = x :=
  lp.ext (funext fun i => by simp [lpOfLinf_apply, linfOfLp_apply])

/-- A continuous multilinear form on `ℓ^∞(ℕ)` is a bounded multilinear form. -/
theorem isBddML_continuousMultilinearMap {d : ℕ}
    (f : ContinuousMultilinearMap K (fun _ : Fin d => Linf K) K) :
    IsBddML (fun u => f u) ‖f‖ where
  add u j v w := f.map_update_add u j v w
  smul u j c v := by rw [f.map_update_smul, smul_eq_mul]
  bound u := f.le_opNorm u

/-! ### The tail property on `ℓ^∞(I)` -/

/-- The tail property on `ℓ^∞(I)` under `NSC`. -/
theorem tail_lp_of_nsc [IsUltrametricDist K] [CompleteSpace K] (hK : NSC K)
    [Countable I] [Infinite I] {d : ℕ}
    (μ : ContinuousMultilinearMap K (fun _ : Fin d => lp (fun _ : I => K) ∞) K)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ S : Finset I, ∀ x : Fin d → lp (fun _ : I => K) ∞, (∀ r, ‖x r‖ ≤ 1) →
      (∃ r, ∀ i ∈ S, (x r : I → K) i = 0) → ‖μ x‖ ≤ ε := by
  classical
  obtain ⟨hD⟩ := nonempty_denumerable I
  let e : I ≃ ℕ := Denumerable.eqv I
  let Φ := μ.compContinuousLinearMap (fun _ => lpOfLinf (K := K) e)
  obtain ⟨N, hN⟩ := tail_multilinear hK d (fun u => Φ u) ‖Φ‖
    (isBddML_continuousMultilinearMap Φ) ε hε
  refine ⟨(Finset.range N).image e.symm, fun x hx ⟨r, hr⟩ => ?_⟩
  have hΦ : Φ (fun r => linfOfLp e.symm (x r)) = μ x := by
    simp only [Φ, ContinuousMultilinearMap.compContinuousLinearMap_apply, lpOfLinf_linfOfLp]
  rw [← hΦ]
  refine hN _ (fun j => (norm_linfOfLp_le _ _).trans (hx j)) ⟨r, fun n hn => ?_⟩
  rw [linfOfLp_apply]
  exact hr _ (Finset.mem_image_of_mem _ (Finset.mem_range.2 hn))

/-- Lemma F.2(2): the tail property on `ℓ^∞(I)` when `K` is not spherically complete. -/
theorem multilinear_tail [IsUltrametricDist K] [CompleteSpace K]
    (hK : ¬ SphericallyCompleteSpace K) [Countable I] [Infinite I] {d : ℕ}
    (μ : ContinuousMultilinearMap K (fun _ : Fin d => lp (fun _ : I => K) ∞) K)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ S : Finset I, ∀ x : Fin d → lp (fun _ : I => K) ∞, (∀ r, ‖x r‖ ≤ 1) →
      (∃ r, ∀ i ∈ S, (x r : I → K) i = 0) → ‖μ x‖ ≤ ε :=
  tail_lp_of_nsc (nsc_of_not_sphericallyComplete hK) μ ε hε

/-- Rescaled tail bound: arguments of norm at most `‖c‖` give the bound `‖c‖ ^ d * ε`. -/
theorem norm_le_of_tail {d : ℕ}
    {μ : ContinuousMultilinearMap K (fun _ : Fin d => lp (fun _ : I => K) ∞) K}
    {S : Finset I} {ε : ℝ}
    (hS : ∀ x : Fin d → lp (fun _ : I => K) ∞, (∀ r, ‖x r‖ ≤ 1) →
      (∃ r, ∀ i ∈ S, (x r : I → K) i = 0) → ‖μ x‖ ≤ ε)
    {c : K} (hc : c ≠ 0) (x : Fin d → lp (fun _ : I => K) ∞) (hx : ∀ r, ‖x r‖ ≤ ‖c‖)
    (hxS : ∃ r, ∀ i ∈ S, (x r : I → K) i = 0) : ‖μ x‖ ≤ ‖c‖ ^ d * ε := by
  have hc0 : 0 < ‖c‖ := norm_pos_iff.2 hc
  have hxeq : x = fun r => c • (c⁻¹ • x r) := funext fun r => by rw [smul_inv_smul₀ hc]
  rw [hxeq, μ.map_smul_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin, norm_smul,
    norm_pow]
  refine mul_le_mul_of_nonneg_left (hS _ (fun r => ?_) ?_) (by positivity)
  · rw [norm_smul, norm_inv, inv_mul_le_iff₀ hc0, mul_one]
    exact hx r
  · obtain ⟨r, hr⟩ := hxS
    exact ⟨r, fun i hi => by simp [lp.coeFn_smul, hr i hi]⟩

lemma norm_single_one [DecidableEq I] (i : I) :
    ‖(lp.single ∞ i (1 : K) : lp (fun _ : I => K) ∞)‖ = 1 := by
  rw [lp.norm_single ENNReal.zero_lt_top, norm_one]

/-! ### Consequences: diagonal values and null array -/

/-- Lemma F.2(3): the diagonal values `μ (e_i, …, e_i)` tend to `0` along the cofinite filter. -/
theorem multilinear_diagonal_tendsto_zero [IsUltrametricDist K] [CompleteSpace K]
    (hK : ¬ SphericallyCompleteSpace K) [Countable I] [Infinite I] [DecidableEq I]
    {d : ℕ} (hd : 1 ≤ d)
    (μ : ContinuousMultilinearMap K (fun _ : Fin d => lp (fun _ : I => K) ∞) K) :
    Tendsto (fun i : I => μ (fun _ => lp.single ∞ i (1 : K))) cofinite (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨S, hS⟩ := multilinear_tail hK μ (ε / 2) (half_pos hε)
  refine (S.finite_toSet.subset fun i hi => ?_)
  by_contra hiS
  apply hi
  simp only [Set.mem_ofPred_eq, dist_zero_right]
  refine lt_of_le_of_lt (hS _ (fun _ => (norm_single_one i).le) ⟨⟨0, hd⟩, fun j hj => ?_⟩)
    (half_lt_self hε)
  exact lp.single_apply_ne (E := fun _ : I => K) ∞ i (1 : K) (fun h => hiS (h ▸ hj))

/-- The coefficient array `μ (e_{i_1}, …, e_{i_d})` is null on `I^d`. -/
theorem multilinear_coeff_tendsto_zero [IsUltrametricDist K] [CompleteSpace K]
    (hK : ¬ SphericallyCompleteSpace K) [Countable I] [Infinite I] [DecidableEq I] {d : ℕ}
    (μ : ContinuousMultilinearMap K (fun _ : Fin d => lp (fun _ : I => K) ∞) K) :
    Tendsto (fun i : Fin d → I => μ (fun r => lp.single ∞ (i r) (1 : K))) cofinite (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨S, hS⟩ := multilinear_tail hK μ (ε / 2) (half_pos hε)
  refine ((Fintype.piFinset fun _ : Fin d => S).finite_toSet.subset fun i hi => ?_)
  by_contra hiS
  apply hi
  rw [Finset.mem_coe, Fintype.mem_piFinset] at hiS
  push Not at hiS
  obtain ⟨r, hr⟩ := hiS
  simp only [Set.mem_ofPred_eq, dist_zero_right]
  refine lt_of_le_of_lt (hS _ (fun _ => (norm_single_one _).le) ⟨r, fun j hj => ?_⟩)
    (half_lt_self hε)
  exact lp.single_apply_ne (E := fun _ : I => K) ∞ (i r) (1 : K) (fun h => hr (h ▸ hj))

end AlternatingAnalytic.Tails
