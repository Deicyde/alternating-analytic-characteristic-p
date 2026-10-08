import AlternatingAnalytic.Scalar.Tails.LpTails

/-!
# The coefficient expansion of a multilinear form on `ℓ^∞(I, K)`

Let `K` be complete, nonarchimedean and not spherically complete, and `I` countably infinite.
For a continuous `d`-linear form `μ` on `ℓ^∞(I, K)` and `x ∈ ℓ^∞(I, K)^d`,
`μ x` is the unconditional sum over `i ∈ I^d` of `μ (e_{i_1}, …, e_{i_d}) x^1_{i_1} ⋯ x^d_{i_d}`
(`multilinear_hasSum`; formula (F.1) of the paper). Given the finite set `S` of the tail property,
the partial sum over `S^d` is `μ` evaluated at the restrictions of the `x^r` to `S`
(`restrictLp`); the difference from `μ x` expands into terms with one slot vanishing on `S`, and
the remaining terms of the sum also have one slot vanishing on `S`, so the ultrametric inequality
bounds everything by the tail bound.
-/

namespace AlternatingAnalytic.Tails

open Filter Topology
open scoped ENNReal

variable {K : Type*} [NontriviallyNormedField K] {I : Type*} [DecidableEq I]

/-- The restriction `∑_{s ∈ S} x_s e_s` of `x ∈ ℓ^∞(I)` to `S`. -/
noncomputable def restrictLp (S : Finset I) (x : lp (fun _ : I => K) ∞) :
    lp (fun _ : I => K) ∞ :=
  ∑ s ∈ S, x s • lp.single ∞ s (1 : K)

lemma restrictLp_apply (S : Finset I) (x : lp (fun _ : I => K) ∞) (i : I) :
    restrictLp S x i = if i ∈ S then x i else 0 := by
  rw [restrictLp, lp.coeFn_sum, Finset.sum_apply]
  simp only [lp.coeFn_smul, Pi.smul_apply, lp.single_apply, Pi.single_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero]
  exact Finset.sum_ite_eq S i x

lemma norm_restrictLp_le (S : Finset I) (x : lp (fun _ : I => K) ∞) :
    ‖restrictLp S x‖ ≤ ‖x‖ :=
  lp.norm_le_of_forall_le (norm_nonneg x) fun i => by
    rw [restrictLp_apply]
    split_ifs
    · exact lp.norm_apply_le_norm ENNReal.top_ne_zero x i
    · simp

lemma norm_sub_restrictLp_le (S : Finset I) (x : lp (fun _ : I => K) ∞) :
    ‖x - restrictLp S x‖ ≤ ‖x‖ :=
  lp.norm_le_of_forall_le (norm_nonneg x) fun i => by
    rw [lp.coeFn_sub, Pi.sub_apply, restrictLp_apply]
    split_ifs
    · simp
    · rw [sub_zero]; exact lp.norm_apply_le_norm ENNReal.top_ne_zero x i

lemma sub_restrictLp_apply_of_mem {S : Finset I} (x : lp (fun _ : I => K) ∞) {i : I}
    (hi : i ∈ S) : (x - restrictLp S x) i = 0 := by
  rw [lp.coeFn_sub, Pi.sub_apply, restrictLp_apply, ite_eq_left hi, sub_self]

/-- **Expansion (F.1).** `μ x` is the unconditional sum of
`μ (e_{i_1}, …, e_{i_d}) x^1_{i_1} ⋯ x^d_{i_d}` over `i ∈ I^d`. -/
theorem multilinear_hasSum [IsUltrametricDist K] [CompleteSpace K]
    (hK : ¬ SphericallyCompleteSpace K) [Countable I] [Infinite I] {d : ℕ}
    (μ : ContinuousMultilinearMap K (fun _ : Fin d => lp (fun _ : I => K) ∞) K)
    (x : Fin d → lp (fun _ : I => K) ∞) :
    HasSum
      (fun i : Fin d → I => μ (fun r => lp.single ∞ (i r) (1 : K)) * ∏ r, (x r : I → K) (i r))
      (μ x) := by
  obtain ⟨c, hc⟩ := NormedField.exists_lt_norm K (∑ r, ‖x r‖)
  have hsum0 : 0 ≤ ∑ r, ‖x r‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hc0 : c ≠ 0 := norm_pos_iff.1 (hsum0.trans_lt hc)
  have hxc : ∀ r, ‖x r‖ ≤ ‖c‖ := fun r =>
    (Finset.single_le_sum (fun j _ => norm_nonneg (x j)) (Finset.mem_univ r)).trans hc.le
  have hcpos : 0 < ‖c‖ ^ d := pow_pos (norm_pos_iff.2 hc0) d
  change Tendsto (fun s : Finset (Fin d → I) => ∑ i ∈ s,
    μ (fun r => lp.single ∞ (i r) (1 : K)) * ∏ r, (x r : I → K) (i r)) atTop (𝓝 (μ x))
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨S, hS⟩ := multilinear_tail hK μ ((δ / 2) / ‖c‖ ^ d) (div_pos (half_pos hδ) hcpos)
  have hbound : ∀ y : Fin d → lp (fun _ : I => K) ∞, (∀ r, ‖y r‖ ≤ ‖c‖) →
      (∃ r, ∀ i ∈ S, (y r : I → K) i = 0) → ‖μ y‖ ≤ δ / 2 := fun y hy hyS =>
    (norm_le_of_tail hS hc0 y hy hyS).trans_eq (by field_simp)
  have hterm : ∀ i : Fin d → I, μ (fun r => lp.single ∞ (i r) (1 : K)) *
      ∏ r, (x r : I → K) (i r) =
      μ (fun r => (x r : I → K) (i r) • lp.single ∞ (i r) (1 : K)) := by
    intro i
    rw [μ.map_smul_univ, smul_eq_mul, mul_comm]
  set P := Fintype.piFinset fun _ : Fin d => S with hPdef
  refine ⟨P, fun F hF => ?_⟩
  have hout : ∀ i ∈ F \ P, ‖μ (fun r => lp.single ∞ (i r) (1 : K)) *
      ∏ r, (x r : I → K) (i r)‖ ≤ δ / 2 := by
    intro i hi
    have hiP : i ∉ P := (Finset.mem_sdiff.1 hi).2
    rw [hPdef, Fintype.mem_piFinset] at hiP
    push Not at hiP
    obtain ⟨r, hr⟩ := hiP
    rw [hterm]
    refine hbound _ (fun j => ?_) ⟨r, fun j hj => ?_⟩
    · rw [norm_smul, norm_single_one, mul_one]
      exact (lp.norm_apply_le_norm ENNReal.top_ne_zero _ _).trans (hxc j)
    · rw [lp.coeFn_smul, Pi.smul_apply,
        lp.single_apply_ne (E := fun _ : I => K) ∞ _ _ (fun h : j = i r => hr (h ▸ hj)), smul_zero]
  have hP : ∑ i ∈ P, μ (fun r => lp.single ∞ (i r) (1 : K)) * ∏ r, (x r : I → K) (i r) =
      μ (fun r => restrictLp S (x r)) := by
    simp_rw [hterm]
    exact (μ.map_sum_finset (fun r s => (x r : I → K) s • lp.single ∞ s (1 : K))
      (fun _ => S)).symm
  have hdiff : ‖μ x - μ (fun r => restrictLp S (x r))‖ ≤ δ / 2 := by
    set m : Fin d → lp (fun _ : I => K) ∞ := fun r => restrictLp S (x r) with hm
    set m' : Fin d → lp (fun _ : I => K) ∞ := fun r => x r - restrictLp S (x r) with hm'
    have hx : x = m + m' := funext fun r => by simp [hm, hm']
    have hsum : μ x = ∑ s : Finset (Fin d), μ (s.piecewise m m') := by
      conv_lhs => rw [hx]
      exact μ.map_add_univ m m'
    rw [hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ Finset.univ), Finset.piecewise_univ,
      add_sub_cancel_left]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (half_pos hδ).le fun s hs => ?_
    have hs' : s ≠ Finset.univ := Finset.ne_of_mem_erase hs
    obtain ⟨r, hr⟩ : ∃ r, r ∉ s := by
      by_contra h
      push Not at h
      exact hs' (Finset.eq_univ_iff_forall.2 h)
    refine hbound _ (fun j => ?_) ⟨r, fun i hi => ?_⟩
    · by_cases hj : j ∈ s
      · rw [Finset.piecewise_eq_of_mem _ _ _ hj]
        exact (norm_restrictLp_le _ _).trans (hxc j)
      · rw [Finset.piecewise_eq_of_notMem _ _ _ hj]
        exact (norm_sub_restrictLp_le _ _).trans (hxc j)
    · rw [Finset.piecewise_eq_of_notMem _ _ _ hr]
      exact sub_restrictLp_apply_of_mem _ hi
  rw [dist_eq_norm, ← Finset.sum_sdiff hF, hP]
  have hrw : ∑ i ∈ F \ P, μ (fun r => lp.single ∞ (i r) (1 : K)) * ∏ r, (x r : I → K) (i r) +
      μ (fun r => restrictLp S (x r)) - μ x =
      ∑ i ∈ F \ P, μ (fun r => lp.single ∞ (i r) (1 : K)) * ∏ r, (x r : I → K) (i r) +
      -(μ x - μ (fun r => restrictLp S (x r))) := by ring
  rw [hrw]
  refine lt_of_le_of_lt ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_))
    (half_lt_self hδ)
  · exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (half_pos hδ).le hout
  · rw [norm_neg]; exact hdiff

/-- **Lemma F.2, part 1.** The coefficient array is null and gives the expansion (F.1). -/
theorem multilinear_expansion [IsUltrametricDist K] [CompleteSpace K]
    (hK : ¬ SphericallyCompleteSpace K) [Countable I] [Infinite I] {d : ℕ}
    (μ : ContinuousMultilinearMap K (fun _ : Fin d => lp (fun _ : I => K) ∞) K) :
    Tendsto (fun i : Fin d → I => μ (fun r => lp.single ∞ (i r) (1 : K))) cofinite (𝓝 0) ∧
      ∀ x : Fin d → lp (fun _ : I => K) ∞,
        HasSum
          (fun i : Fin d → I =>
            μ (fun r => lp.single ∞ (i r) (1 : K)) * ∏ r, (x r : I → K) (i r))
          (μ x) :=
  ⟨multilinear_coeff_tendsto_zero hK μ, multilinear_hasSum hK μ⟩

end AlternatingAnalytic.Tails
