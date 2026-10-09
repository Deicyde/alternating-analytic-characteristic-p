import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Lemma A.1 (one-variable uniqueness), p. 25

Paper statement: "Let K be nontrivially normed and Z a normed K-space, not necessarily
complete. Let z₀, z₁, … ∈ Z, ρ > 0 and M ≥ 0 with ‖zₙ‖ρⁿ ≤ M for all n. If ∑ₙ tⁿ zₙ
converges to 0 for every t ∈ K with |t| < ρ, then zₙ = 0 for all n."

Formalization notes:
* No completeness of `K` or `Z` is assumed, as in the paper.
* "∑ₙ tⁿ zₙ converges to 0" is read as convergence of the ordered partial sums
  `∑_{n<N} tⁿ • zₙ → 0` (`Filter.Tendsto` along `atTop`), not as unconditional summation
  (`HasSum`). Under the bound `‖zₙ‖ρⁿ ≤ M` the two readings agree, but the partial-sum
  reading is the literal one.
* The hypothesis `M ≥ 0` is kept although it follows from the bound at `n = 0`.
* No definitions are introduced.
-/

open Filter Topology

namespace AlternatingAnalyticChallenge.LemA_1

/-- **Lemma A.1.** If `‖z n‖ ρ ^ n ≤ M` for all `n` and the partial sums of `∑ tⁿ z n` tend
to `0` for every `t` with `‖t‖ < ρ`, then every `z n` is zero. `Z` need not be complete. -/
theorem one_variable_uniqueness
    (K : Type*) [NontriviallyNormedField K]
    (Z : Type*) [NormedAddCommGroup Z] [NormedSpace K Z]
    (z : ℕ → Z) (ρ M : ℝ) (hρ : 0 < ρ) (hM : 0 ≤ M)
    (hbound : ∀ n, ‖z n‖ * ρ ^ n ≤ M)
    (hconv : ∀ t : K, ‖t‖ < ρ →
      Tendsto (fun N => ∑ n ∈ Finset.range N, t ^ n • z n) atTop (𝓝 0)) :
    ∀ n, z n = 0 := by
  -- Package the coefficients as a one-variable formal multilinear series representing `0`
  -- on the ball of radius `ρ`, then apply Mathlib's `HasFPowerSeriesAt.apply_eq_zero`
  -- (no completeness assumption).
  let p : FormalMultilinearSeries K K Z := fun n =>
    ContinuousMultilinearMap.mkPiRing K (Fin n) (z n)
  have hp_apply : ∀ (n : ℕ) (t : K), (p n fun _ => t) = t ^ n • z n := by
    intro n t
    simp [p, ContinuousMultilinearMap.mkPiRing_apply, Finset.prod_const]
  let ρ' : NNReal := ⟨ρ, hρ.le⟩
  have hrad : (ρ' : ENNReal) ≤ p.radius := by
    refine p.le_radius_of_bound M (fun n => ?_)
    change ‖p n‖ * ρ ^ n ≤ M
    simpa [p, ContinuousMultilinearMap.norm_mkPiRing] using hbound n
  have hball : HasFPowerSeriesOnBall (fun _ : K => (0 : Z)) p 0 ρ' :=
    { r_le := hrad
      r_pos := ENNReal.coe_pos.mpr (NNReal.coe_pos.mp hρ)
      hasSum := fun {y} hy => by
        have hy' : ‖y‖ < ρ := by
          have := Metric.mem_eball.mp hy
          rw [edist_zero_right, enorm_eq_nnnorm] at this
          exact NNReal.coe_lt_coe.mpr (ENNReal.coe_lt_coe.mp this)
        have hsn : Summable fun n => ‖p n fun _ => y‖ :=
          p.summable_norm_apply (Metric.eball_subset_eball hrad hy)
        rw [hasSum_iff_tendsto_nat_of_summable_norm hsn]
        simpa [hp_apply] using hconv y hy' }
  have h0 : HasFPowerSeriesAt (0 : K → Z) p 0 := hball.hasFPowerSeriesAt
  intro n
  simpa [hp_apply] using h0.apply_eq_zero n 1

end AlternatingAnalyticChallenge.LemA_1
