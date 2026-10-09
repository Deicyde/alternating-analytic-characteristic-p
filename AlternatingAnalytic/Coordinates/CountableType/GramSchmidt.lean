import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Ultra

/-!
# Van der Put's orthogonal bases by approximate Gram–Schmidt

Let `K` be a complete nontrivially normed field and `M` an ultrametric normed `K`-space that is
spanned, as a vector space, by a countable set. Approximate Gram–Schmidt produces a Hamel basis
`b` of `M`, indexed by a subset of `ℕ`, whose coordinate functionals satisfy
`‖b.coord i y‖ * ‖b i‖ ≤ 2 * ‖y‖` (`exists_basis_coord_bound`). The `n`-th vector is `x n` minus
an approximate best approximation from the span of the earlier vectors, with tolerances whose
product stays above `1 / 2`. This is the form of van der Put's basis theorem used in the proof
of Proposition I.1; `M` need not be complete.
-/

noncomputable section

open Metric

namespace AlternatingAnalytic.CountableType

/-- The orthogonality level reached after `n` Gram–Schmidt steps. -/
def gsLevel (n : ℕ) : ℝ := 1 / 2 + (1 / 2) ^ (n + 1)

theorem half_lt_gsLevel (n : ℕ) : 1 / 2 < gsLevel n := by
  unfold gsLevel; have := pow_pos (by norm_num : (0 : ℝ) < 1 / 2) (n + 1); linarith

theorem gsLevel_pos (n : ℕ) : 0 < gsLevel n := lt_trans (by norm_num) (half_lt_gsLevel n)

theorem gsLevel_le_one (n : ℕ) : gsLevel n ≤ 1 := by
  unfold gsLevel
  have : (1 / 2 : ℝ) ^ (n + 1) ≤ 1 / 2 := by
    rw [pow_succ]
    have := pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) (n := n)
    nlinarith
  linarith

theorem gsLevel_succ_lt (n : ℕ) : gsLevel (n + 1) < gsLevel n := by
  unfold gsLevel
  have h := pow_pos (by norm_num : (0 : ℝ) < 1 / 2) (n + 1)
  rw [pow_succ (1 / 2 : ℝ) (n + 1)]
  linarith

/-- The tolerance of the `n`-th Gram–Schmidt step. -/
def gsRatio (n : ℕ) : ℝ := gsLevel (n + 1) / gsLevel n

theorem gsRatio_pos (n : ℕ) : 0 < gsRatio n := div_pos (gsLevel_pos _) (gsLevel_pos _)

theorem gsRatio_lt_one (n : ℕ) : gsRatio n < 1 :=
  (div_lt_one (gsLevel_pos n)).mpr (gsLevel_succ_lt n)

theorem gsLevel_succ_eq (n : ℕ) : gsLevel (n + 1) = gsRatio n * gsLevel n := by
  unfold gsRatio; field_simp [(gsLevel_pos n).ne']

variable (K : Type*) {M : Type*} [NontriviallyNormedField K] [NormedAddCommGroup M]
  [NormedSpace K M]

/-- The span of the first `n` vectors of a sequence. -/
def gsSpan (x : ℕ → M) (n : ℕ) : Submodule K M := Submodule.span K (x '' Set.Iio n)

variable {K}

theorem gsSpan_mono (x : ℕ → M) : Monotone (gsSpan K x) := fun _ _ h =>
  Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio h))

theorem mem_gsSpan_succ (x : ℕ → M) (n : ℕ) : x n ∈ gsSpan K x (n + 1) :=
  Submodule.subset_span ⟨n, Set.mem_Iio.mpr (Nat.lt_succ_self n), rfl⟩

instance (x : ℕ → M) (n : ℕ) : FiniteDimensional K (gsSpan K x n) :=
  FiniteDimensional.span_of_finite K ((Set.finite_Iio n).image x)

/-- A closed subspace contains a `t`-approximate best approximation of every vector. -/
theorem exists_approx_mem (W : Submodule K M) (hW : IsClosed (W : Set M)) (y : M) {t : ℝ}
    (ht1 : t < 1) : ∃ w ∈ W, t * ‖y - w‖ ≤ infDist y (W : Set M) := by
  have hne : (W : Set M).Nonempty := ⟨0, W.zero_mem⟩
  by_cases h : infDist y (W : Set M) = 0
  · exact ⟨y, (hW.mem_iff_infDist_zero hne).mpr h, by simp [h]⟩
  · have hpos : 0 < infDist y (W : Set M) := lt_of_le_of_ne infDist_nonneg (Ne.symm h)
    by_cases ht : t ≤ 0
    · exact ⟨0, W.zero_mem, le_trans (mul_nonpos_of_nonpos_of_nonneg ht (norm_nonneg _))
        hpos.le⟩
    rw [not_le] at ht
    have hlt : infDist y (W : Set M) < infDist y (W : Set M) / t := by
      rw [lt_div_iff₀ ht]; nlinarith
    obtain ⟨w, hw, hdist⟩ := (infDist_lt_iff hne).mp hlt
    refine ⟨w, hw, ?_⟩
    rw [← dist_eq_norm]
    have := (lt_div_iff₀ ht).mp hdist
    linarith

variable [CompleteSpace K]

theorem isClosed_gsSpan (x : ℕ → M) (n : ℕ) : IsClosed (gsSpan K x n : Set M) :=
  Submodule.closed_of_finiteDimensional _

/-- The approximate best approximation of `x n` from the span of the earlier vectors. -/
def gsApprox (x : ℕ → M) (n : ℕ) : M :=
  (exists_approx_mem (gsSpan K x n) (isClosed_gsSpan x n) (x n) (gsRatio_lt_one n)).choose

theorem gsApprox_mem (x : ℕ → M) (n : ℕ) : gsApprox (K := K) x n ∈ gsSpan K x n :=
  (exists_approx_mem (gsSpan K x n) (isClosed_gsSpan x n) (x n) (gsRatio_lt_one n)).choose_spec.1

theorem gsApprox_spec (x : ℕ → M) (n : ℕ) :
    gsRatio n * ‖x n - gsApprox (K := K) x n‖ ≤ infDist (x n) (gsSpan K x n : Set M) :=
  (exists_approx_mem (gsSpan K x n) (isClosed_gsSpan x n) (x n) (gsRatio_lt_one n)).choose_spec.2

variable (K) in
/-- The `n`-th Gram–Schmidt vector. -/
def gsVec (x : ℕ → M) (n : ℕ) : M := x n - gsApprox (K := K) x n

theorem gsVec_mem (x : ℕ → M) (n : ℕ) : gsVec K x n ∈ gsSpan K x (n + 1) :=
  Submodule.sub_mem _ (mem_gsSpan_succ x n) (gsSpan_mono x (Nat.le_succ n) (gsApprox_mem x n))

theorem gsVec_mem_of_lt (x : ℕ → M) {m N : ℕ} (h : m < N) : gsVec K x m ∈ gsSpan K x N :=
  gsSpan_mono x h (gsVec_mem x m)

/-- The new vector keeps its distance from the earlier span, up to the step tolerance. -/
theorem gsRatio_mul_le_norm_smul_add (x : ℕ → M) (n : ℕ) (c : K) {w : M}
    (hw : w ∈ gsSpan K x n) : gsRatio n * (‖c‖ * ‖gsVec K x n‖) ≤ ‖c • gsVec K x n + w‖ := by
  by_cases hc : c = 0
  · simp [hc]
  have hmem : gsApprox (K := K) x n - c⁻¹ • w ∈ gsSpan K x n :=
    Submodule.sub_mem _ (gsApprox_mem x n) (Submodule.smul_mem _ _ hw)
  have hd := infDist_le_dist_of_mem (x := x n) hmem
  rw [dist_eq_norm] at hd
  have heq : c • gsVec K x n + w = c • (x n - (gsApprox (K := K) x n - c⁻¹ • w)) := by
    simp only [gsVec, smul_sub, smul_smul, mul_inv_cancel₀ hc, one_smul]
    abel
  rw [heq, norm_smul]
  have hspec := gsApprox_spec (K := K) x n
  calc gsRatio n * (‖c‖ * ‖gsVec K x n‖) = ‖c‖ * (gsRatio n * ‖x n - gsApprox (K := K) x n‖) := by
        unfold gsVec; ring
    _ ≤ ‖c‖ * ‖x n - (gsApprox (K := K) x n - c⁻¹ • w)‖ :=
        mul_le_mul_of_nonneg_left (hspec.trans hd) (norm_nonneg _)

variable [IsUltrametricDist M]

theorem norm_sub_le_max_norm (y z : M) : ‖y - z‖ ≤ max ‖y‖ ‖z‖ := by
  simpa [sub_eq_add_neg] using IsUltrametricDist.norm_add_le_max y (-z)

/-- Orthogonality of the first `N` Gram–Schmidt vectors at level `gsLevel N`. -/
theorem gsLevel_mul_le_norm_sum (x : ℕ → M) (N : ℕ) (c : ℕ → K) :
    ∀ n < N, gsLevel N * (‖c n‖ * ‖gsVec K x n‖) ≤
      ‖∑ m ∈ Finset.range N, c m • gsVec K x m‖ := by
  induction N with
  | zero => intro n hn; exact absurd hn (Nat.not_lt_zero n)
  | succ N ih =>
    intro n hn
    set w := ∑ m ∈ Finset.range N, c m • gsVec K x m with hw_def
    have hw : w ∈ gsSpan K x N :=
      Submodule.sum_mem _ fun m hm =>
        Submodule.smul_mem _ _ (gsVec_mem_of_lt x (Finset.mem_range.mp hm))
    rw [Finset.sum_range_succ, ← hw_def, add_comm w]
    set y := c N • gsVec K x N + w with hy
    have h1 : gsRatio N * (‖c N‖ * ‖gsVec K x N‖) ≤ ‖y‖ :=
      gsRatio_mul_le_norm_smul_add x N (c N) hw
    have ht1 : gsRatio N ≤ 1 := (gsRatio_lt_one N).le
    have ht0 : 0 ≤ gsRatio N := (gsRatio_pos N).le
    have h2 : gsRatio N * ‖w‖ ≤ ‖y‖ := by
      have hwy : w = y - c N • gsVec K x N := by rw [hy]; abel
      have hmax := norm_sub_le_max_norm y (c N • gsVec K x N)
      rw [← hwy, norm_smul] at hmax
      calc gsRatio N * ‖w‖ ≤ gsRatio N * max ‖y‖ (‖c N‖ * ‖gsVec K x N‖) :=
            mul_le_mul_of_nonneg_left hmax ht0
        _ = max (gsRatio N * ‖y‖) (gsRatio N * (‖c N‖ * ‖gsVec K x N‖)) :=
            mul_max_of_nonneg _ _ ht0
        _ ≤ ‖y‖ := max_le (by nlinarith [norm_nonneg y]) h1
    rw [gsLevel_succ_eq]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hlt | heq
    · calc gsRatio N * gsLevel N * (‖c n‖ * ‖gsVec K x n‖)
            = gsRatio N * (gsLevel N * (‖c n‖ * ‖gsVec K x n‖)) := by ring
        _ ≤ gsRatio N * ‖w‖ := mul_le_mul_of_nonneg_left (ih n hlt) ht0
        _ ≤ ‖y‖ := h2
    · subst heq
      calc gsRatio n * gsLevel n * (‖c n‖ * ‖gsVec K x n‖)
            ≤ gsRatio n * 1 * (‖c n‖ * ‖gsVec K x n‖) := by
            gcongr
            exact gsLevel_le_one n
        _ ≤ ‖y‖ := by rw [mul_one]; exact h1

/-- Orthogonality, in the form of a coordinate bound for finitely supported combinations of the
nonzero Gram–Schmidt vectors. -/
theorem half_mul_le_norm_linearCombination (x : ℕ → M)
    (l : {n : ℕ // gsVec K x n ≠ 0} →₀ K) (i : {n : ℕ // gsVec K x n ≠ 0}) :
    1 / 2 * (‖l i‖ * ‖gsVec K x i‖) ≤
      ‖Finsupp.linearCombination K (fun j : {n : ℕ // gsVec K x n ≠ 0} => gsVec K x j) l‖ := by
  classical
  by_cases hi : i ∈ l.support
  swap
  · rw [Finsupp.notMem_support_iff.mp hi]; simp
  set N := l.support.sup (fun j => j.val) + 1
  let c : ℕ → K := fun m => if h : gsVec K x m ≠ 0 then l ⟨m, h⟩ else 0
  have hc : ∀ j : {n : ℕ // gsVec K x n ≠ 0}, c j.val = l j := fun j => by simp [c, j.2]
  have hsum : ∑ m ∈ Finset.range N, c m • gsVec K x m =
      Finsupp.linearCombination K (fun j : {n : ℕ // gsVec K x n ≠ 0} => gsVec K x j) l := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    have hmap : ∑ j ∈ l.support, l j • gsVec K x j =
        ∑ m ∈ l.support.map (Function.Embedding.subtype _), c m • gsVec K x m := by
      rw [Finset.sum_map]
      exact Finset.sum_congr rfl fun j _ => by rw [Function.Embedding.subtype_apply, hc]
    rw [hmap]
    symm
    apply Finset.sum_subset
    · intro m hm
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hm
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := fun j => j.val) hj))
    · intro m _ hm
      by_cases h : gsVec K x m = 0
      · simp [h]
      · have hnot : (⟨m, h⟩ : {n : ℕ // gsVec K x n ≠ 0}) ∉ l.support := fun hmem =>
          hm (Finset.mem_map.mpr ⟨⟨m, h⟩, hmem, rfl⟩)
        have : c m = 0 := by
          simpa [c, h] using Finsupp.notMem_support_iff.mp hnot
        simp [this]
  have hiN : i.val < N := Nat.lt_succ_of_le (Finset.le_sup (f := fun j => j.val) hi)
  have h := gsLevel_mul_le_norm_sum x N c i.val hiN
  rw [hsum, hc] at h
  exact le_trans (mul_le_mul_of_nonneg_right (half_lt_gsLevel N).le
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))) h

theorem gsVec_linearIndependent (x : ℕ → M) :
    LinearIndependent K (fun j : {n : ℕ // gsVec K x n ≠ 0} => gsVec K x j) := by
  rw [linearIndependent_iff]
  intro l hl
  ext i
  have h := half_mul_le_norm_linearCombination x l i
  rw [hl, norm_zero] at h
  have hb : 0 < ‖gsVec K x i‖ := norm_pos_iff.mpr i.2
  have : ‖l i‖ * ‖gsVec K x i‖ ≤ 0 := by linarith
  have : ‖l i‖ ≤ 0 := by nlinarith [norm_nonneg (l i)]
  simpa using le_antisymm this (norm_nonneg _)

omit [IsUltrametricDist M] in
theorem mem_span_gsVec (x : ℕ → M) (n : ℕ) :
    x n ∈ Submodule.span K
      (Set.range fun j : {n : ℕ // gsVec K x n ≠ 0} => gsVec K x j) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have happrox : gsApprox (K := K) x n ∈ Submodule.span K
        (Set.range fun j : {n : ℕ // gsVec K x n ≠ 0} => gsVec K x j) := by
      refine Submodule.span_le.mpr ?_ (gsApprox_mem x n)
      rintro _ ⟨m, hm, rfl⟩
      exact ih m (Set.mem_Iio.mp hm)
    have hvec : gsVec K x n ∈ Submodule.span K
        (Set.range fun j : {n : ℕ // gsVec K x n ≠ 0} => gsVec K x j) := by
      by_cases h : gsVec K x n = 0
      · rw [h]; exact Submodule.zero_mem _
      · exact Submodule.subset_span ⟨⟨n, h⟩, rfl⟩
    have : x n = gsVec K x n + gsApprox (K := K) x n := by simp [gsVec]
    rw [this]
    exact Submodule.add_mem _ hvec happrox

/-- Van der Put's basis theorem, countable-span form: a countably spanned ultrametric normed
space over a complete field has a Hamel basis with `‖b.coord i y‖ * ‖b i‖ ≤ 2 ‖y‖`. -/
theorem exists_basis_coord_bound (T : Set M) (hT : T.Countable)
    (hspan : Submodule.span K T = ⊤) :
    ∃ (ι : Type) (_ : LinearOrder ι) (b : Module.Basis ι K M),
      ∀ i y, ‖b.coord i y‖ * ‖b i‖ ≤ 2 * ‖y‖ := by
  obtain ⟨x, hx⟩ := (hT.union (Set.countable_singleton (0 : M))).exists_eq_range
    ⟨0, Or.inr rfl⟩
  have hli := gsVec_linearIndependent (K := K) x
  have hsp : ⊤ ≤ Submodule.span K
      (Set.range fun j : {n : ℕ // gsVec K x n ≠ 0} => gsVec K x j) := by
    rw [← hspan]
    refine Submodule.span_le.mpr fun y hy => ?_
    obtain ⟨n, hn⟩ : y ∈ Set.range x := hx ▸ Or.inl hy
    rw [← hn]
    exact mem_span_gsVec x n
  refine ⟨{n : ℕ // gsVec K x n ≠ 0}, inferInstance, Module.Basis.mk hli hsp, fun i y => ?_⟩
  have h := half_mul_le_norm_linearCombination x ((Module.Basis.mk hli hsp).repr y) i
  have hrepr := (Module.Basis.mk hli hsp).linearCombination_repr y
  rw [Module.Basis.coe_mk] at hrepr
  rw [hrepr] at h
  rw [Module.Basis.coord_apply, Module.Basis.mk_apply]
  linarith

end AlternatingAnalytic.CountableType
