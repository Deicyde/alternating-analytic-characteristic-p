import Mathlib.Analysis.Analytic.CPolynomialDef
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Data.List.TFAE
import AlternatingAnalytic.Descent.OneLift

/-!
# Proposition 3.3 (one lift, every base point), p. 8

Solution: the statements of `Challenges/Prop3_3.lean`, proved from the library:
* `tfae`: `AlternatingAnalytic.OneLift.tfae` (`Descent/OneLift.lean`), applied to the injective
  bounded linear map underlying `j`; the `k`-th coefficient of any power series of `a` is
  identified through the ambient line expansion of `B` (`Round24Transfer.coeff_eq_of_ambient`,
  `Round24Transfer.map_diag_add_smul`); closedness of the range of `j` and `1 ≤ k` are not used;
* `precomposition_dichotomy`:
  `AlternatingAnalytic.OneLift.precomposition_polynomial_or_nowhereAnalytic`
  (`Descent/OneLift.lean`), from `Round24Transfer.hasBoundedLift_of_analyticAt`.
-/

namespace AlternatingAnalyticChallenge.Prop3_3

/-- A continuous polynomial: a finite sum of diagonals of bounded multilinear maps. -/
def IsContinuousPolynomial (K : Type*) [NontriviallyNormedField K]
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace K X]
    [NormedAddCommGroup Y] [NormedSpace K Y] (g : X → Y) : Prop :=
  ∃ (p : FormalMultilinearSeries K X Y) (N : ℕ),
    ∀ x, g x = ∑ n ∈ Finset.range N, p n (fun _ => x)

/-- **Proposition 3.3, equivalence (1) ⇔ (2) ⇔ (3).** -/
theorem tfae
    {K : Type*} [NontriviallyNormedField K]
    {H W Z : Type*} [NormedAddCommGroup H] [NormedSpace K H]
    [NormedAddCommGroup W] [NormedSpace K W] [NormedAddCommGroup Z] [NormedSpace K Z]
    (j : W →ₗᵢ[K] Z) (hj : IsClosed (Set.range j))
    (k : ℕ) (hk : 1 ≤ k) (B : ContinuousMultilinearMap K (fun _ : Fin k => H) Z)
    (a : H → W) (ha : ∀ h, j (a h) = B (fun _ => h)) :
    List.TFAE
      [∃ h₀, AnalyticAt K a h₀,
       ∃ Q : ContinuousMultilinearMap K (fun _ : Fin k => H) W, ∀ h, Q (fun _ => h) = a h,
       ∀ h₀, ∃ (p : FormalMultilinearSeries K H W) (N : ℕ),
         HasFiniteFPowerSeriesOnBall a p h₀ N ⊤] := by
  exact AlternatingAnalytic.OneLift.tfae j.toContinuousLinearMap j.injective k B a ha

/-- **Proposition 3.3, consequence.** Each precomposition action is either a continuous
polynomial on its whole domain or analytic nowhere. -/
theorem precomposition_dichotomy
    {K : Type*} [NontriviallyNormedField K]
    (E E' F : Type*) [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup E'] [NormedSpace K E'] [NormedAddCommGroup F] [NormedSpace K F]
    (k : ℕ) :
    IsContinuousPolynomial K
        (ContinuousAlternatingMap.compContinuousLinearMapCLM :
          (E →L[K] E') → (E' [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F)) ∨
      ∀ f₀ : E →L[K] E', ¬ AnalyticAt K
        (ContinuousAlternatingMap.compContinuousLinearMapCLM :
          (E →L[K] E') → (E' [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F)) f₀ := by
  exact AlternatingAnalytic.OneLift.precomposition_polynomial_or_nowhereAnalytic

end AlternatingAnalyticChallenge.Prop3_3
