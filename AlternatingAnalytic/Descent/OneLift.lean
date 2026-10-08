import AlternatingAnalytic.Analysis.LiftCriterion
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Data.List.TFAE

/-!
# One lift, every base point

For a map `a : H → W` whose image under an injective bounded linear map `j : W → Z` is the
diagonal of a bounded `k`-linear map `B : H^k → Z`, analyticity of `a` at a single point already
forces `a` to be the diagonal of a bounded `k`-linear map `H^k → W`, and then `a` has a finite
power-series expansion of infinite radius at every point. The `k`-th coefficient of any power
series of `a` is identified through the ambient line expansion of `B`
(`Round24Transfer.coeff_eq_of_ambient`, `Round24Transfer.map_diag_add_smul`). As a consequence the
precomposition action on continuous alternating maps is either a continuous polynomial on its
whole domain or analytic nowhere. No completeness is assumed anywhere.
-/

namespace AlternatingAnalytic.OneLift

open Round24Transfer

variable {K : Type*} [NontriviallyNormedField K]
  {H W Z : Type*} [NormedAddCommGroup H] [NormedSpace K H]
  [NormedAddCommGroup W] [NormedSpace K W] [NormedAddCommGroup Z] [NormedSpace K Z]

/-- The diagonal of a bounded `n`-linear map has a finite power series of infinite radius
at `0`. -/
theorem hasFiniteFPowerSeriesOnBall_diag_zero {n : ℕ}
    (P : ContinuousMultilinearMap K (fun _ : Fin n => H) W) :
    HasFiniteFPowerSeriesOnBall (fun x => P (fun _ => x))
      (P.toFormalMultilinearSeries.compContinuousLinearMap
        (ContinuousLinearMap.pi fun _ : Fin n => ContinuousLinearMap.id K H)) 0 (n + 1) ⊤ := by
  have hP := P.hasFiniteFPowerSeriesOnBall
  rw [Fintype.card_fin] at hP
  refine HasFiniteFPowerSeriesOnBall.mk' (fun m hm => ?_) ENNReal.zero_lt_top (fun y _ => ?_)
  · ext v
    simp [FormalMultilinearSeries.compContinuousLinearMap_apply, hP.finite m hm]
  · have h := hP.eq_partialSum (fun _ => y) (by simp) (n + 1) le_rfl
    rw [zero_add] at h
    simp only [zero_add, FormalMultilinearSeries.compContinuousLinearMap_apply]
    rw [FormalMultilinearSeries.partialSum] at h
    rw [h]
    rfl

/-- The diagonal of a bounded `n`-linear map has a finite power series of infinite radius
at every point. -/
theorem exists_hasFiniteFPowerSeriesOnBall_of_diag {n : ℕ}
    (P : ContinuousMultilinearMap K (fun _ : Fin n => H) W) (a : H → W)
    (hP : ∀ h, P (fun _ => h) = a h) (h₀ : H) :
    ∃ (p : FormalMultilinearSeries K H W) (N : ℕ),
      HasFiniteFPowerSeriesOnBall a p h₀ N ⊤ := by
  have ha : (fun x => P (fun _ => x)) = a := funext hP
  have h := (hasFiniteFPowerSeriesOnBall_diag_zero P).changeOrigin (y := h₀) ENNReal.coe_lt_top
  rw [ha, zero_add, ENNReal.top_sub_coe] at h
  exact ⟨_, _, h⟩

/-- A finite power series of infinite radius at `0` expresses a map as a finite sum of
diagonals of bounded multilinear maps. -/
theorem eq_sum_of_hasFiniteFPowerSeriesOnBall_zero {g : H → W}
    {p : FormalMultilinearSeries K H W} {N : ℕ} (hg : HasFiniteFPowerSeriesOnBall g p 0 N ⊤)
    (x : H) : g x = ∑ n ∈ Finset.range N, p n (fun _ => x) := by
  have h := hg.eq_partialSum x (by simp) N le_rfl
  rwa [zero_add] at h

/-- **One lift from one point.** If `j ∘ a` is the diagonal of a bounded `k`-linear map and `a`
has a power series at some point, then the `k`-th coefficient of that series is a bounded
`k`-linear lift of `a`. -/
theorem coeff_eq_of_hasFPowerSeriesAt (j : W →L[K] Z) (hj : Function.Injective j) (k : ℕ)
    (B : ContinuousMultilinearMap K (fun _ : Fin k => H) Z)
    (a : H → W) (ha : ∀ h, j (a h) = B (fun _ => h))
    {p : FormalMultilinearSeries K H W} {h₀ : H} (hp : HasFPowerSeriesAt a p h₀) (h : H) :
    p k (fun _ => h) = a h := by
  classical
  refine coeff_eq_of_ambient a h₀ k (fun r x => lineCoeff B h₀ r x) j hj a
    (fun t x => ?_) (fun x => ?_) p hp h
  · rw [ha, map_diag_add_smul B h₀ x t, Fintype.card_fin]
  · have := lineCoeff_card B h₀ x
    rw [Fintype.card_fin] at this
    rw [this, ha]

/-- **Proposition 3.3, (1) ⇒ (2).** -/
theorem exists_lift_of_analyticAt (j : W →L[K] Z) (hj : Function.Injective j) (k : ℕ)
    (B : ContinuousMultilinearMap K (fun _ : Fin k => H) Z)
    (a : H → W) (ha : ∀ h, j (a h) = B (fun _ => h)) {h₀ : H} (hfa : AnalyticAt K a h₀) :
    ∃ Q : ContinuousMultilinearMap K (fun _ : Fin k => H) W, ∀ h, Q (fun _ => h) = a h := by
  obtain ⟨p, hp⟩ := hfa
  exact ⟨p k, coeff_eq_of_hasFPowerSeriesAt j hj k B a ha hp⟩

/-- **Proposition 3.3.** For `a : H → W` with `j ∘ a` the diagonal of a bounded `k`-linear map,
analytic somewhere ⟺ bounded `k`-linear lift ⟺ finite power series of infinite radius
everywhere. -/
theorem tfae (j : W →L[K] Z) (hj : Function.Injective j) (k : ℕ)
    (B : ContinuousMultilinearMap K (fun _ : Fin k => H) Z)
    (a : H → W) (ha : ∀ h, j (a h) = B (fun _ => h)) :
    List.TFAE
      [∃ h₀, AnalyticAt K a h₀,
       ∃ Q : ContinuousMultilinearMap K (fun _ : Fin k => H) W, ∀ h, Q (fun _ => h) = a h,
       ∀ h₀, ∃ (p : FormalMultilinearSeries K H W) (N : ℕ),
         HasFiniteFPowerSeriesOnBall a p h₀ N ⊤] := by
  tfae_have 1 → 2 := fun ⟨_, h⟩ => exists_lift_of_analyticAt j hj k B a ha h
  tfae_have 2 → 3 := fun ⟨Q, hQ⟩ h₀ =>
    exists_hasFiniteFPowerSeriesOnBall_of_diag Q a hQ h₀
  tfae_have 3 → 1 := fun h => by
    obtain ⟨p, N, hp⟩ := h 0
    exact ⟨0, hp.toHasFPowerSeriesOnBall.analyticAt⟩
  tfae_finish

section Precomposition

variable {ι : Type*} [Fintype ι]
  {E E' F : Type*} [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup E'] [NormedSpace K E'] [NormedAddCommGroup F] [NormedSpace K F]

/-- **Dichotomy for precomposition.** The action `A^k` is a finite sum of diagonals of bounded
multilinear maps on its whole domain, or analytic nowhere. -/
theorem precomposition_polynomial_or_nowhereAnalytic :
    (∃ (p : FormalMultilinearSeries K (E →L[K] E')
        ((E' [⋀^ι]→L[K] F) →L[K] (E [⋀^ι]→L[K] F))) (N : ℕ),
      ∀ f, Q K ι E E' F f = ∑ n ∈ Finset.range N, p n (fun _ => f)) ∨
      ∀ f₀, ¬ AnalyticAt K (Q K ι E E' F) f₀ := by
  by_cases hL : HasBoundedLift K ι E E' F
  · obtain ⟨P, hP⟩ := hL
    obtain ⟨p, N, hp⟩ := exists_hasFiniteFPowerSeriesOnBall_of_diag (K := K) (H := E →L[K] E')
      (W := (E' [⋀^ι]→L[K] F) →L[K] (E [⋀^ι]→L[K] F)) P (Q K ι E E' F) hP 0
    exact Or.inl ⟨p, N, eq_sum_of_hasFiniteFPowerSeriesOnBall_zero hp⟩
  · exact Or.inr fun _ h => hL (hasBoundedLift_of_analyticAt h)

end Precomposition

end AlternatingAnalytic.OneLift
