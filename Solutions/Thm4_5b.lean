import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Within
import AlternatingAnalytic.Analysis.L1FixedDegreeReflection

/-!
# Proof of Theorem 4.5(2)

Uses `analyticOn_comp_of_l1_fixed_degree_isometry` and
`analyticOnNhd_comp_of_l1_fixed_degree_isometry` (`Analysis/L1FixedDegreeReflection.lean`).
The retract clause is proved here: pull back along `r`, apply the ℓ¹ case, restrict along `i`.
-/

namespace AlternatingAnalyticChallenge.Thm4_5b

universe uI uK uH uW uZ uP

/-- Theorem 4.5(2): if `j (a h) = B (h, …, h)` for a bounded `d`-linear `B`, then `a ∘ γ` is
analytic on `U ⊆ ℓ¹(I, K)` for every `γ` analytic on `U`. -/
theorem l1_analyticOn_comp_of_fixed_degree_representation
    {I : Type uI} {K : Type uK} [NontriviallyNormedField K]
    {H : Type uH} [NormedAddCommGroup H] [NormedSpace K H]
    {W : Type uW} [NormedAddCommGroup W] [NormedSpace K W]
    {Z : Type uZ} [NormedAddCommGroup Z] [NormedSpace K Z] [CompleteSpace Z]
    (j : W →ₗᵢ[K] Z) (hj : IsClosed (Set.range j)) (d : ℕ)
    (B : ContinuousMultilinearMap K (fun _ : Fin d => H) Z)
    (a : H → W) (ha : ∀ h, j (a h) = B (fun _ => h))
    {U : Set (lp (fun _ : I => K) 1)} (hU : IsOpen U)
    {γ : lp (fun _ : I => K) 1 → H} (hγ : AnalyticOn K γ U) :
    AnalyticOn K (a ∘ γ) U := by
  exact AlternatingAnalytic.analyticOn_comp_of_l1_fixed_degree_isometry j hj d B a ha hU hγ

/-- Theorem 4.5(2), retracts: the same conclusion on a bounded linear retract `P` of
`ℓ¹(I, K)`. -/
theorem l1_retract_analyticOn_comp_of_fixed_degree_representation
    {I : Type uI} {K : Type uK} [NontriviallyNormedField K]
    {H : Type uH} [NormedAddCommGroup H] [NormedSpace K H]
    {W : Type uW} [NormedAddCommGroup W] [NormedSpace K W]
    {Z : Type uZ} [NormedAddCommGroup Z] [NormedSpace K Z] [CompleteSpace Z]
    {P : Type uP} [NormedAddCommGroup P] [NormedSpace K P]
    (i : P →L[K] lp (fun _ : I => K) 1) (r : lp (fun _ : I => K) 1 →L[K] P)
    (hri : r.comp i = ContinuousLinearMap.id K P)
    (j : W →ₗᵢ[K] Z) (hj : IsClosed (Set.range j)) (d : ℕ)
    (B : ContinuousMultilinearMap K (fun _ : Fin d => H) Z)
    (a : H → W) (ha : ∀ h, j (a h) = B (fun _ => h))
    {U : Set P} (hU : IsOpen U)
    {γ : P → H} (hγ : AnalyticOn K γ U) :
    AnalyticOn K (a ∘ γ) U := by
  have hri_apply (x : P) : r (i x) = x := DFunLike.congr_fun hri x
  have hpull : AnalyticOnNhd K (γ ∘ r) (r ⁻¹' U) :=
    (hU.analyticOn_iff_analyticOnNhd.mp hγ).comp (r.analyticOnNhd _) (fun _ hx => hx)
  have hfr : AnalyticOnNhd K (a ∘ (γ ∘ r)) (r ⁻¹' U) :=
    AlternatingAnalytic.analyticOnNhd_comp_of_l1_fixed_degree_isometry j hj d B a ha hpull
  have hmaps : Set.MapsTo i U (r ⁻¹' U) := by
    intro x hx
    change r (i x) ∈ U
    rwa [hri_apply]
  have hcomp : (a ∘ (γ ∘ r)) ∘ i = a ∘ γ := by
    funext x
    exact congrArg (fun y => a (γ y)) (hri_apply x)
  have h := hfr.comp (i.analyticOnNhd U) hmaps
  rw [hcomp] at h
  exact h.analyticOn

end AlternatingAnalyticChallenge.Thm4_5b
