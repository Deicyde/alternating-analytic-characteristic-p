import AlternatingAnalytic.Laurent.FiniteDimSharp.CZeroSpherical
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

/-!
# Orthonormal sequences in discretely normed ultrametric spaces

Let `X` be an ultrametric normed space over `K` whose nonzero norms are integral powers of `e > 1`,
with every power `e ^ n` the norm of a scalar. Distances to a closed subspace `W` are then attained,
and rescaling a nearest-point remainder gives a unit vector `v` with
`‖w + c • v‖ = max ‖w‖ ‖c‖` for all `w ∈ W` (`exists_orthogonal_unit`). Iterating over the growing
finite-dimensional spans gives an orthonormal sequence in an infinite-dimensional `X`
(`exists_orthonormal_seq`); if `X` is complete, `a ↦ ∑' n, a n • v n` is a linear isometry
`C₀(ℕ, K) → X` (`exists_cZero_linearIsometry`). This replaces Serre's orthonormal-basis theorem
in the proof of Corollary C.8.
-/

open Filter Topology
open scoped ZeroAtInfty BoundedContinuousFunction

namespace AlternatingAnalytic.FiniteDimSharp

variable {K X : Type*} [NontriviallyNormedField K] [NormedAddCommGroup X] [NormedSpace K X]
  [IsUltrametricDist X] {e : ℝ}

omit [IsUltrametricDist X] in
/-- With discrete norms, every point outside a closed subspace has a nearest point in it. -/
theorem exists_nearest (he : 1 < e) (hX : ∀ x : X, x ≠ 0 → ∃ n : ℤ, ‖x‖ = e ^ n)
    (W : Submodule K X) (hW : IsClosed (W : Set X)) {y : X} (hy : y ∉ W) :
    ∃ w₀ ∈ W, ∀ w ∈ W, ‖y - w₀‖ ≤ ‖y - w‖ := by
  have hcl : y ∉ closure (W : Set X) := by rwa [hW.closure_eq]
  rw [Metric.mem_closure_iff] at hcl
  push Not at hcl
  obtain ⟨ε, hε, hεW⟩ := hcl
  have hne : ∀ w ∈ W, y - w ≠ 0 := fun w hw h => hy (by rw [sub_eq_zero.mp h]; exact hw)
  let S : Set ℤ := {n | ∃ w ∈ W, ‖y - w‖ = e ^ n}
  have hSne : S.Nonempty := by
    obtain ⟨n, hn⟩ := hX (y - 0) (hne 0 W.zero_mem)
    exact ⟨n, 0, W.zero_mem, hn⟩
  obtain ⟨m, hm⟩ : ∃ m : ℕ, e⁻¹ ^ m < ε := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ he)
  have hSbdd : BddBelow S := by
    refine ⟨-(m : ℤ), fun n ⟨w, hw, hn⟩ => ?_⟩
    have h1 : ε ≤ e ^ n := by rw [← hn, ← dist_eq_norm]; exact hεW w hw
    have h2 : e ^ (-(m : ℤ)) < e ^ n := by
      calc e ^ (-(m : ℤ)) = e⁻¹ ^ m := by rw [zpow_neg, zpow_natCast, inv_pow]
        _ < ε := hm
        _ ≤ e ^ n := h1
    exact ((zpow_lt_zpow_iff_right₀ he).mp h2).le
  obtain ⟨w₀, hw₀, hn₀⟩ := Int.csInf_mem hSne hSbdd
  refine ⟨w₀, hw₀, fun w hw => ?_⟩
  obtain ⟨n, hn⟩ := hX _ (hne w hw)
  rw [hn₀, hn]
  exact zpow_le_zpow_right₀ he.le (csInf_le hSbdd ⟨w, hw, hn⟩)

/-- A unit vector orthogonal, in the ultrametric sense, to a proper closed subspace. -/
theorem exists_orthogonal_unit (he : 1 < e) (hX : ∀ x : X, x ≠ 0 → ∃ n : ℤ, ‖x‖ = e ^ n)
    (hK : ∀ n : ℤ, ∃ c : K, ‖c‖ = e ^ n)
    (W : Submodule K X) (hW : IsClosed (W : Set X)) (htop : W ≠ ⊤) :
    ∃ v : X, ‖v‖ = 1 ∧ ∀ w ∈ W, ∀ c : K, ‖w + c • v‖ = max ‖w‖ ‖c‖ := by
  have he0 : 0 < e := zero_lt_one.trans he
  obtain ⟨y, hy⟩ : ∃ y, y ∉ W := by
    by_contra h
    push Not at h
    exact htop (eq_top_iff.mpr fun x _ => h x)
  obtain ⟨w₀, hw₀, hmin⟩ := exists_nearest he hX W hW hy
  set z := y - w₀ with hz
  have hz0 : z ≠ 0 := fun h => hy (by rw [sub_eq_zero.mp h]; exact hw₀)
  have hzmin : ∀ w ∈ W, ‖z‖ ≤ ‖z - w‖ := fun w hw => by
    have := hmin (w₀ + w) (W.add_mem hw₀ hw)
    rwa [← sub_sub] at this
  obtain ⟨n, hn⟩ := hX z hz0
  obtain ⟨c₀, hc₀⟩ := hK (-n)
  have hc₀z : ‖c₀‖ * ‖z‖ = 1 := by
    rw [hc₀, hn, ← zpow_add₀ he0.ne', neg_add_cancel, zpow_zero]
  have hc₀0 : c₀ ≠ 0 := by
    rintro rfl
    rw [norm_zero, zero_mul] at hc₀z
    exact zero_ne_one hc₀z
  have hv : ‖c₀ • z‖ = 1 := by rw [norm_smul, hc₀z]
  refine ⟨c₀ • z, hv, fun w hw c => ?_⟩
  have hcv : ‖c • (c₀ • z)‖ = ‖c‖ := by rw [norm_smul, hv, mul_one]
  have hlow : ‖c‖ ≤ ‖w + c • (c₀ • z)‖ := by
    rcases eq_or_ne c 0 with rfl | hc
    · simp
    have hcc : c * c₀ ≠ 0 := mul_ne_zero hc hc₀0
    have hw' : -((c * c₀)⁻¹ • w) ∈ W := W.neg_mem (W.smul_mem _ hw)
    have heq : w + c • (c₀ • z) = (c * c₀) • (z - -((c * c₀)⁻¹ • w)) := by
      rw [sub_neg_eq_add, smul_add, smul_smul (c * c₀), mul_inv_cancel₀ hcc, one_smul, smul_smul,
        add_comm]
    rw [heq, norm_smul, norm_mul]
    calc ‖c‖ = ‖c‖ * (‖c₀‖ * ‖z‖) := by rw [hc₀z, mul_one]
      _ ≤ ‖c‖ * (‖c₀‖ * ‖z - -((c * c₀)⁻¹ • w)‖) := by
        gcongr
        exact hzmin _ hw'
      _ = ‖c‖ * ‖c₀‖ * ‖z - -((c * c₀)⁻¹ • w)‖ := by ring
  apply le_antisymm
  · exact (IsUltrametricDist.norm_add_le_max _ _).trans_eq (by rw [hcv])
  · rcases lt_or_ge ‖c‖ ‖w‖ with h | h
    · rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hcv]; exact h.ne'), hcv]
    · exact (max_eq_right h).trans_le hlow

variable [CompleteSpace K]

/-- An infinite-dimensional discretely normed ultrametric space contains an orthonormal
sequence. -/
theorem exists_orthonormal_seq (he : 1 < e) (hX : ∀ x : X, x ≠ 0 → ∃ n : ℤ, ‖x‖ = e ^ n)
    (hK : ∀ n : ℤ, ∃ c : K, ‖c‖ = e ^ n) (hinf : ¬ FiniteDimensional K X) :
    ∃ v : ℕ → X, (∀ n, ‖v n‖ = 1) ∧
      ∀ (n : ℕ) (a : ℕ → K) (i : ℕ), i < n → ‖a i‖ ≤ ‖∑ j ∈ Finset.range n, a j • v j‖ := by
  classical
  have hstep : ∀ W : Submodule K X, FiniteDimensional K W →
      ∃ v : X, ‖v‖ = 1 ∧ ∀ w ∈ W, ∀ c : K, ‖w + c • v‖ = max ‖w‖ ‖c‖ := by
    intro W hW
    refine exists_orthogonal_unit he hX hK W W.closed_of_finiteDimensional ?_
    rintro rfl
    exact hinf (Submodule.topEquiv.finiteDimensional)
  choose! next hnext1 hnext2 using hstep
  let W : ℕ → Submodule K X := fun n =>
    Nat.rec (motive := fun _ => Submodule K X) ⊥ (fun _ V => V ⊔ K ∙ next V) n
  have hWsucc : ∀ n, W (n + 1) = W n ⊔ K ∙ next (W n) := fun n => rfl
  have hWfin : ∀ n : ℕ, FiniteDimensional K ↥(W n) := by
    intro n
    induction n with
    | zero => exact (show FiniteDimensional K (⊥ : Submodule K X) by infer_instance)
    | succ n ih => rw [hWsucc]; infer_instance
  refine ⟨fun n => next (W n), fun n => hnext1 _ (hWfin n), ?_⟩
  have hmem : ∀ n (a : ℕ → K), ∑ j ∈ Finset.range n, a j • next (W j) ∈ W n := by
    intro n a
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, hWsucc]
      exact add_mem (Submodule.mem_sup_left ih)
        (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
  intro n a i hi
  induction n with
  | zero => exact absurd hi (Nat.not_lt_zero _)
  | succ n ih =>
    rw [Finset.sum_range_succ, hnext2 _ (hWfin n) _ (hmem n a) (a n)]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
    · exact (ih h).trans (le_max_left _ _)
    · exact le_max_right _ _

omit [CompleteSpace K] in
/-- An orthonormal sequence in a complete ultrametric space gives a linear isometry
`a ↦ ∑' n, a n • v n` from `C₀(ℕ, K)`. -/
theorem exists_cZero_linearIsometry [CompleteSpace X] (v : ℕ → X) (hv1 : ∀ n, ‖v n‖ = 1)
    (hv2 : ∀ (n : ℕ) (a : ℕ → K) (i : ℕ), i < n → ‖a i‖ ≤ ‖∑ j ∈ Finset.range n, a j • v j‖) :
    ∃ ι : C₀(ℕ, K) →ₗᵢ[K] X, ∀ a, HasSum (fun n => a n • v n) (ι a) := by
  have hsum : ∀ a : C₀(ℕ, K), Summable (fun n => a n • v n) := by
    intro a
    apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    have ha : Tendsto (fun n => a n) cofinite (𝓝 0) := by
      have := a.zero_at_infty'
      rwa [Filter.cocompact_eq_cofinite] at this
    rw [tendsto_zero_iff_norm_tendsto_zero] at ha ⊢
    simpa [norm_smul, hv1] using ha
  let L : C₀(ℕ, K) →ₗ[K] X :=
    { toFun := fun a => ∑' n, a n • v n
      map_add' := fun a b => by
        refine (((hsum a).hasSum.add (hsum b).hasSum).congr_fun fun n => ?_).tsum_eq
        simp [add_smul]
      map_smul' := fun c a => by
        refine (((hsum a).hasSum.const_smul c).congr_fun fun n => ?_).tsum_eq
        simp [smul_smul] }
  refine ⟨{ toLinearMap := L, norm_map' := fun a => ?_ }, fun a => (hsum a).hasSum⟩
  have hlim := (hsum a).hasSum.tendsto_sum_nat.norm
  apply le_antisymm
  · refine le_of_tendsto hlim (Eventually.of_forall fun n => ?_)
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg a) fun i _ => ?_
    rw [norm_smul, hv1, mul_one]
    exact norm_apply_le_norm_cZero a i
  · rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    refine (BoundedContinuousFunction.norm_le (norm_nonneg _)).2 fun i => ?_
    exact ge_of_tendsto hlim (eventually_atTop.2 ⟨i + 1, fun n hn => hv2 n a i (by omega)⟩)

end AlternatingAnalytic.FiniteDimSharp
