import AlternatingAnalytic.Analysis.L1WordSeries
import AlternatingAnalytic.Analysis.L1WordSynthesis
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Normed.Module.Completion

/-!
# Local analytic factorization through ordinary ℓ¹

The word coordinates remain in the original scalar field, which need not be complete.
Only the linear synthesis map takes values in the completion of the output space.
-/

open scoped lp BigOperators ENNReal
open Filter Topology

noncomputable section

namespace L1Coordinates

variable {K I H : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup H] [NormedSpace K H]

local instance : DecidableEq I := Classical.decEq I
local instance : DecidableEq (Words I) := Classical.decEq _

/-- Choose one nonzero scalar inside the expansion ball and a uniform coefficient bound. -/
theorem exists_scalar_coefficient_bound
    {γ : lp (fun _ : I => K) 1 → H}
    {p : FormalMultilinearSeries K (lp (fun _ : I => K) 1) H}
    {x₀ : lp (fun _ : I => K) 1} {r : ℝ≥0∞}
    (hp : HasFPowerSeriesOnBall γ p x₀ r) :
    ∃ s : K, s ≠ 0 ∧ ‖s‖ₑ < r ∧
      ∃ M : ℝ, 0 < M ∧ ∀ n, ‖p n‖ * ‖s‖ ^ n ≤ M := by
  obtain ⟨s, hs, hsr⟩ := NormedField.exists_enorm_lt K hp.r_pos
  obtain ⟨M, hM, hpM⟩ := p.norm_mul_pow_le_of_lt_radius (h := hsr.trans_le hp.r_le)
  exact ⟨s, by simpa using ne_of_gt hs, hsr, M, hM, hpM⟩

/-- The formal series of the actual multilinear word blocks. -/
def wordSeries (s : K) : FormalMultilinearSeries K (L1 K I) (L1 K (Words I)) :=
  wordBlock s

theorem wordSeries_radius (s : K) (hs : s ≠ 0) :
    ‖s‖ₑ ≤ (wordSeries (I := I) s).radius := by
  apply (wordSeries s).le_radius_of_bound 1 (r := ‖s‖₊)
  intro n
  calc
    ‖wordSeries (I := I) s n‖ * ‖s‖ ^ n ≤ ‖s⁻¹‖ ^ n * ‖s‖ ^ n :=
      mul_le_mul_of_nonneg_right (norm_wordBlock_le s n) (by positivity)
    _ = 1 := by
      rw [← mul_pow, norm_inv, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hs), one_pow]

/-- The explicit word vector has its word-block expansion on the full scalar-norm ball. -/
theorem geometricWordVector_hasFPowerSeriesOnBall (s : K) (hs : s ≠ 0) (x₀ : L1 K I) :
    HasFPowerSeriesOnBall (fun x => geometricWordVector s (x - x₀))
      (wordSeries s) x₀ ‖s‖ₑ where
  r_le := wordSeries_radius s hs
  r_pos := by simpa using hs
  hasSum := by
    intro y hy
    have hyn : ‖y‖ < ‖s‖ := by
      simpa only [mem_eball_zero_iff, enorm, ENNReal.coe_lt_coe,
        ← NNReal.coe_lt_coe, coe_nnnorm] using hy
    simpa only [add_sub_cancel_left, wordSeries] using hasSum_wordBlock s hyn

/-- Synthesis sends the explicit geometric vector to the original analytic function. -/
theorem wordSynthesis_geometricWordVector
    {γ : L1 K I → H} {p : FormalMultilinearSeries K (L1 K I) H}
    {x₀ : L1 K I} {r : ℝ≥0∞} (hp : HasFPowerSeriesOnBall γ p x₀ r)
    (s : K) (hs : s ≠ 0) (hsr : ‖s‖ₑ < r)
    (M : ℝ) (hpM : ∀ n, ‖p n‖ * ‖s‖ ^ n ≤ M)
    {y : L1 K I} (hy : ‖y - x₀‖ < ‖s‖) :
    wordSynthesis p s M hpM (geometricWordVector s (y - x₀)) =
      (γ y : UniformSpace.Completion H) := by
  have hyr : y ∈ Metric.eball x₀ r := by
    apply lt_trans ?_ hsr
    simpa only [edist_eq_enorm_sub, enorm, ENNReal.coe_lt_coe,
      ← NNReal.coe_lt_coe, coe_nnnorm] using hy
  have hg : HasSum
      (fun n => (p n (fun _ => y - x₀) : UniformSpace.Completion H))
      (wordSynthesis p s M hpM (geometricWordVector s (y - x₀))) := by
    simpa only [wordSynthesis_wordBlock p s hs M hpM] using
      (wordSynthesis p s M hpM).hasSum (hasSum_wordBlock s hy)
  exact hg.unique
    ((UniformSpace.Completion.toComplL : H →L[K] UniformSpace.Completion H).hasSum
      (hp.hasSum_sub hyr))

/-- Quantitative local factorization through ordinary scalar-valued ℓ¹ on all finite words.

The same scalar, bound, synthesis map, explicit word vector, and actual word-block series
satisfy every conclusion. No completeness of the scalar field or of `H` is assumed, and
the degree-zero coordinate retains the value at the expansion point, even for empty `I`.
-/
theorem l1_word_factorization
    {γ : L1 K I → H} {p : FormalMultilinearSeries K (L1 K I) H}
    {x₀ : L1 K I} {r : ℝ≥0∞} (hp : HasFPowerSeriesOnBall γ p x₀ r) :
    ∃ (s : K) (M : ℝ) (T : L1 K (Words I) →L[K] UniformSpace.Completion H)
      (g : L1 K I → L1 K (Words I))
      (q : FormalMultilinearSeries K (L1 K I) (L1 K (Words I))),
      s ≠ 0 ∧ ‖s‖ₑ < r ∧ 0 < M ∧
      (∀ n, ‖p n‖ * ‖s‖ ^ n ≤ M) ∧ ‖T‖ ≤ M ∧
      (∀ n (a : Fin n → I), T (lp.single 1 ⟨n, a⟩ (1 : K)) =
        s ^ n • (p n (fun i => lp.single 1 (a i) (1 : K)) :
          UniformSpace.Completion H)) ∧
      q = wordSeries s ∧ HasFPowerSeriesOnBall g q x₀ ‖s‖ₑ ∧
      (∀ n, ‖q n‖ ≤ ‖s⁻¹‖ ^ n) ∧
      (∀ n (v : Fin n → L1 K I) (a : Fin n → I),
        q n v ⟨n, a⟩ = (s⁻¹) ^ n * ∏ i, v i (a i)) ∧
      (∀ n (v : Fin n → L1 K I) m (a : Fin m → I), m ≠ n →
        q n v ⟨m, a⟩ = 0) ∧
      (∀ y, ‖y - x₀‖ < ‖s‖ →
        (∀ n (a : Fin n → I), g y ⟨n, a⟩ = (s⁻¹) ^ n * ∏ i, (y - x₀) (a i)) ∧
        T (g y) = (γ y : UniformSpace.Completion H)) ∧
      (∀ y, ¬‖y - x₀‖ < ‖s‖ → g y = 0) ∧
      (∀ a : Fin 0 → I, g x₀ ⟨0, a⟩ = 1 ∧
        T (lp.single 1 ⟨0, a⟩ (1 : K)) = (γ x₀ : UniformSpace.Completion H)) := by
  obtain ⟨s, hs, hsr, M, hM, hpM⟩ := exists_scalar_coefficient_bound hp
  refine ⟨s, M, wordSynthesis p s M hpM,
    (fun y => geometricWordVector s (y - x₀)), wordSeries s,
    hs, hsr, hM, hpM, norm_wordSynthesis_le p s M hM.le hpM,
    wordSynthesis_single p s M hpM, rfl,
    geometricWordVector_hasFPowerSeriesOnBall s hs x₀,
    norm_wordBlock_le s, wordBlock_apply_same s, ?_, ?_, ?_, ?_⟩
  · intro n v m a hmn
    exact wordBlock_apply_ne s n v a hmn
  · intro y hy
    exact ⟨geometricWordVector_apply hy,
      wordSynthesis_geometricWordVector hp s hs hsr M hpM hy⟩
  · intro y hy
    exact geometricWordVector_of_not_lt hy
  · intro a
    constructor
    · apply geometricWordVector_apply_zero
      simpa using (norm_pos_iff.mpr hs)
    · rw [wordSynthesis_single, pow_zero, one_smul, hp.coeff_zero]

/-- Every analytic map on ordinary ℓ¹ locally factors through a bounded linear map
from ordinary ℓ¹ on finite words into the completion of its output. -/
theorem exists_analyticAt_l1_factorization
    {γ : L1 K I → H} {x₀ : L1 K I} (hγ : AnalyticAt K γ x₀) :
    ∃ (T : L1 K (Words I) →L[K] UniformSpace.Completion H)
      (g : L1 K I → L1 K (Words I)),
      AnalyticAt K g x₀ ∧
      (fun x => T (g x)) =ᶠ[𝓝 x₀]
        (fun x => (γ x : UniformSpace.Completion H)) := by
  obtain ⟨p, r, hp⟩ := hγ
  obtain ⟨s, M, T, g, q, hs, _, _, _, _, _, _, hg, _, _, _, hlocal, _, _⟩ :=
    l1_word_factorization hp
  refine ⟨T, g, hg.analyticAt, ?_⟩
  filter_upwards [Metric.ball_mem_nhds x₀ (norm_pos_iff.mpr hs)] with y hy
  exact (hlocal y (by simpa only [Metric.mem_ball, dist_eq_norm] using hy)).2

end L1Coordinates
