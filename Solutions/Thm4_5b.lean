import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Within
import AlternatingAnalytic.Analysis.L1FixedDegreeReflection

/-!
# Theorem 4.5(2) (summable parameter spaces: ℓ¹), p. 11

Solution: identical statements to `Challenges/Thm4_5b.lean`, proved from
`AlternatingAnalytic.analyticOn_comp_of_l1_fixed_degree_isometry` and
`AlternatingAnalytic.analyticOnNhd_comp_of_l1_fixed_degree_isometry`
(`Analysis/L1FixedDegreeReflection.lean`). The retract clause for this reflection statement is
not in the library (only for the family corollary in `Analysis/L1Families.lean`); it is derived
here in a few lines (pull back along `r`, apply the ℓ¹ theorem, restrict along `i`).
-/

namespace AlternatingAnalyticChallenge.Thm4_5b

universe uI uK uH uW uZ uP

/-- **Theorem 4.5(2).** `Z` complete, `j : W → Z` a closed linear isometry, and `a : H → W`
with an ambient bounded homogeneous polynomial representation of fixed degree `d`
(`j (a h) = B (h, …, h)` for a bounded `d`-linear `B : H^d → Z`). For every `γ : U → H`
analytic on an open `U ⊆ ℓ¹(I, K)`, the composite `a ∘ γ` is analytic on `U`. -/
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

/-- **Theorem 4.5(2), bounded linear retract clause.** The same conclusion for a parameter
space `P` that is a bounded linear retract of `ℓ¹(I, K)`: `i : P → ℓ¹(I, K)` and
`r : ℓ¹(I, K) → P` bounded linear with `r ∘ i = id_P`. -/
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
