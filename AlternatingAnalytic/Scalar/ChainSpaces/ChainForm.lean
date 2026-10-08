import AlternatingAnalytic.Scalar.ChainSpaces.Operators
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# The chain forms `m_c`

Fix a `j`-chain sequence `s`, an idempotent residual `ρ' j` on `V'` and a continuous alternating
form `δ` on `V'` vanishing on `(ker ρ' j)^k` (in the paper, the determinant on `K^k`, which
vanishes on the hyperplane `Σ'^j`). For `z` in the chain-limit space `E' = chainSpace ρ'` the
values `δ(z_{1,w}, …, z_{k,w})` tend to zero along the chain (`tendsto_chain_form`). Over a
complete nonarchimedean field the series
`m_c(z) = ∑ₙ c_{s n} δ(z_{1,s n}, …, z_{k,s n})` therefore converges for every bounded `c`
(F.11), and `c ↦ m_c` is a continuous linear map `ℓ^∞(List L, K) → Alt(E'; K)` (`chainForm`).
At the coordinate vector of a chain word it is the evaluation form `δ'_{s n}`
(`chainForm_single`).
-/

open Filter Topology
open scoped ENNReal

namespace AlternatingAnalytic.ChainSpaces

variable {K : Type*} [NontriviallyNormedField K] {L : Type*}
  {V' : Type*} [NormedAddCommGroup V'] [NormedSpace K V'] (ρ' : L → V' →L[K] V')
  {ι : Type*} [Fintype ι]

theorem norm_evalForm_apply_le (δ : V' [⋀^ι]→L[K] K) (i : List L) (z : ι → chainSpace ρ') :
    ‖evalForm ρ' δ i z‖ ≤ ‖δ‖ * ∏ r, ‖z r‖ :=
  (δ.le_opNorm _).trans (mul_le_mul_of_nonneg_left
    (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      (fun _ _ => lp.norm_apply_le_norm ENNReal.top_ne_zero _ _)) (norm_nonneg _))

/-- Along a `j`-chain, `δ(z_{1,w}, …, z_{k,w}) → 0` for `z` in the chain-limit space, provided `δ`
vanishes on `(ker ρ' j)^k`. -/
theorem tendsto_chain_form {j : L} {s : ℕ → List L} (hs : IsChainSeq j s)
    (hidem' : ∀ v, ρ' j (ρ' j v) = ρ' j v) (δ : V' [⋀^ι]→L[K] K)
    (hδ : ∀ z : ι → V', (∀ r, ρ' j (z r) = 0) → δ z = 0) (z : ι → chainSpace ρ') :
    Tendsto (fun n => evalForm ρ' δ (s n) z) atTop (𝓝 0) := by
  set m₁ : ℕ → ι → V' := fun n r => (z r : lp (fun _ : List L => V') ∞) (s n) with hm₁
  set m₂ : ℕ → ι → V' := fun n r => m₁ n r - ρ' j (m₁ n r) with hm₂
  have hzero : ∀ n, δ (m₂ n) = 0 := fun n => hδ _ fun r => by
    simp only [m₂, map_sub, hidem', sub_self]
  have hdiff : Tendsto (fun n => m₁ n - m₂ n) atTop (𝓝 0) := by
    have h : (fun n => m₁ n - m₂ n) = fun n r => ρ' j (m₁ n r) := by
      funext n r
      simp only [m₂, Pi.sub_apply, sub_sub_cancel]
    rw [h]
    exact tendsto_pi_nhds.2 fun r => (z r).2 j s hs
  set C : ℝ := (1 + ‖ρ' j‖) * ∑ r, ‖z r‖ with hC
  have hsum0 : 0 ≤ ∑ r, ‖z r‖ := Finset.sum_nonneg fun r _ => norm_nonneg _
  have hC0 : 0 ≤ C := mul_nonneg (by positivity) hsum0
  have hz : ∀ n r, ‖m₁ n r‖ ≤ ‖z r‖ := fun n r =>
    lp.norm_apply_le_norm ENNReal.top_ne_zero _ _
  have hsum : ∀ r, ‖z r‖ ≤ ∑ r, ‖z r‖ := fun r =>
    Finset.single_le_sum (fun r _ => norm_nonneg (z r)) (Finset.mem_univ r)
  have h1 : ∀ n, ‖m₁ n‖ ≤ C := fun n => (pi_norm_le_iff_of_nonneg hC0).2 fun r => by
    calc ‖m₁ n r‖ ≤ ∑ r, ‖z r‖ := (hz n r).trans (hsum r)
      _ ≤ C := le_mul_of_one_le_left hsum0 (by simp)
  have h2 : ∀ n, ‖m₂ n‖ ≤ C := fun n => (pi_norm_le_iff_of_nonneg hC0).2 fun r => by
    calc ‖m₂ n r‖ ≤ ‖m₁ n r‖ + ‖ρ' j‖ * ‖m₁ n r‖ :=
          (norm_sub_le _ _).trans (add_le_add_right ((ρ' j).le_opNorm _) _)
      _ = (1 + ‖ρ' j‖) * ‖m₁ n r‖ := by ring
      _ ≤ C := mul_le_mul_of_nonneg_left ((hz n r).trans (hsum r)) (by positivity)
  have hbound : ∀ n, ‖evalForm ρ' δ (s n) z‖ ≤
      ‖δ‖ * Fintype.card ι * C ^ (Fintype.card ι - 1) * ‖m₁ n - m₂ n‖ := fun n => by
    have := δ.norm_image_sub_le (m₁ n) (m₂ n)
    rw [hzero, sub_zero] at this
    refine this.trans ?_
    gcongr
    exact max_le (h1 n) (h2 n)
  have hlim : Tendsto (fun n => ‖δ‖ * Fintype.card ι * C ^ (Fintype.card ι - 1) *
      ‖m₁ n - m₂ n‖) atTop (𝓝 0) := by
    have := hdiff.norm.const_mul (‖δ‖ * Fintype.card ι * C ^ (Fintype.card ι - 1))
    rwa [norm_zero, mul_zero] at this
  exact squeeze_zero_norm hbound hlim

variable [CompleteSpace K] [IsUltrametricDist K]

section ChainForm

variable {j : L} {s : ℕ → List L} (hs : IsChainSeq j s) (hidem' : ∀ v, ρ' j (ρ' j v) = ρ' j v)
  (δ : V' [⋀^ι]→L[K] K) (hδ : ∀ z : ι → V', (∀ r, ρ' j (z r) = 0) → δ z = 0)

include hs hidem' hδ in
theorem summable_chain_form (c : lp (fun _ : List L => K) ∞) (z : ι → chainSpace ρ') :
    Summable (fun n => c (s n) * evalForm ρ' δ (s n) z) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop]
  have h := (tendsto_chain_form ρ' hs hidem' δ hδ z).norm.const_mul ‖c‖
  rw [norm_zero, mul_zero] at h
  refine squeeze_zero_norm (fun n => ?_) h
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (lp.norm_apply_le_norm ENNReal.top_ne_zero c (s n))
    (norm_nonneg _)

/-- The alternating form `m_c(z) = ∑ₙ c_{s n} δ(z_{·, s n})` (algebraic version). -/
noncomputable def chainFormAlt (c : lp (fun _ : List L => K) ∞) : chainSpace ρ' [⋀^ι]→ₗ[K] K where
  toFun z := ∑' n, c (s n) * evalForm ρ' δ (s n) z
  map_update_add' z i x y := by
    simp only [ContinuousAlternatingMap.map_update_add, mul_add]
    exact (summable_chain_form ρ' hs hidem' δ hδ c _).tsum_add
      (summable_chain_form ρ' hs hidem' δ hδ c _)
  map_update_smul' z i a x := by
    simp only [ContinuousAlternatingMap.map_update_smul, smul_eq_mul]
    rw [← tsum_mul_left]
    congr 1
    funext n
    ring
  map_eq_zero_of_eq' z i i' h hne := by
    simp only [(evalForm ρ' δ _).map_eq_zero_of_eq z h hne, mul_zero, tsum_zero]

theorem chainFormAlt_apply (c : lp (fun _ : List L => K) ∞) (z : ι → chainSpace ρ') :
    chainFormAlt ρ' hs hidem' δ hδ c z = ∑' n, c (s n) * evalForm ρ' δ (s n) z :=
  rfl

theorem norm_chainFormAlt_apply_le (c : lp (fun _ : List L => K) ∞) (z : ι → chainSpace ρ') :
    ‖chainFormAlt ρ' hs hidem' δ hδ c z‖ ≤ ‖c‖ * ‖δ‖ * ∏ r, ‖z r‖ := by
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun n => ?_
  rw [norm_mul, mul_assoc]
  exact mul_le_mul (lp.norm_apply_le_norm ENNReal.top_ne_zero c (s n))
    (norm_evalForm_apply_le ρ' δ (s n) z) (norm_nonneg _) (norm_nonneg _)

/-- `c ↦ m_c` as a continuous linear map `ℓ^∞(List L, K) → Alt(E'; K)` (F.11). -/
noncomputable def chainForm : lp (fun _ : List L => K) ∞ →L[K] (chainSpace ρ' [⋀^ι]→L[K] K) :=
  LinearMap.mkContinuous
    { toFun := fun c => (chainFormAlt ρ' hs hidem' δ hδ c).mkContinuous (‖c‖ * ‖δ‖)
        (norm_chainFormAlt_apply_le ρ' hs hidem' δ hδ c)
      map_add' := fun c c' => by
        ext z
        simp only [AlternatingMap.coe_mkContinuous, ContinuousAlternatingMap.add_apply,
          chainFormAlt_apply, lp.coeFn_add, Pi.add_apply, add_mul]
        exact (summable_chain_form ρ' hs hidem' δ hδ c z).tsum_add
          (summable_chain_form ρ' hs hidem' δ hδ c' z)
      map_smul' := fun a c => by
        ext z
        simp only [AlternatingMap.coe_mkContinuous, ContinuousAlternatingMap.smul_apply,
          chainFormAlt_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [← tsum_mul_left]
        congr 1
        funext n
        ring }
    ‖δ‖ fun c => by
      refine ContinuousAlternatingMap.opNorm_le_bound _ (by positivity) fun z => ?_
      rw [mul_comm ‖δ‖ ‖c‖]
      exact norm_chainFormAlt_apply_le ρ' hs hidem' δ hδ c z

theorem chainForm_apply (c : lp (fun _ : List L => K) ∞) (z : ι → chainSpace ρ') :
    chainForm ρ' hs hidem' δ hδ c z = ∑' n, c (s n) * evalForm ρ' δ (s n) z :=
  rfl

/-- At the coordinate vector of a chain word, `m_{e_{s n}} = δ'_{s n}`. -/
theorem chainForm_single [DecidableEq L] (n : ℕ) :
    chainForm ρ' hs hidem' δ hδ (lp.single ∞ (s n) 1) = evalForm ρ' δ (s n) := by
  ext z
  rw [chainForm_apply, tsum_eq_single n]
  · rw [lp.single_apply_self, one_mul]
  · intro m hm
    rw [lp.single_apply_ne ∞ (s n) _ (fun h => hm (hs.injective h)), zero_mul]

end ChainForm

end AlternatingAnalytic.ChainSpaces
