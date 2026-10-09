import Mathlib.Analysis.Analytic.CPolynomialDef
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Data.List.TFAE

/-!
# Proposition 3.3 (one lift, every base point), p. 8

Standing assumptions of Section 3: "`K` is nontrivially normed, `P, W, Z` are normed `K`-spaces,
and `j : W → Z` is a linear isometry with closed range. None of these spaces is assumed complete."
Just before the proposition: "We call a finite sum of diagonals of bounded multilinear maps a
continuous polynomial."

Paper statement: "Let `k ≥ 1`, and suppose `a : H → W` satisfies `j a(h) = B(h, …, h)` for a
bounded `k`-linear map `B : H^k → Z`. The following are equivalent:
(1) `a` is analytic at some point of `H`;
(2) there is a bounded `k`-linear `Q : H^k → W` with `Q(h, …, h) = a(h)`;
(3) `a` has a finite power-series expansion at every point, of infinite radius.
Consequently each precomposition action `A^k_{E,E';F}` is either a continuous polynomial on its
whole domain or analytic nowhere."
Here (Section 2.2) `A^k_{E,E';F} : L(E, E') → L(Alt^k(E'; F), Alt^k(E; F))`,
`A(f)(m) = m ∘ (f, …, f)`.

## Formalization notes
* `H` is any normed `K`-space.
* (3) is `∀ h₀, ∃ p N, HasFiniteFPowerSeriesOnBall a p h₀ N ⊤`.
* `IsContinuousPolynomial g` says `g x = ∑_{n < N} p_n(x, …, x)` for a `FormalMultilinearSeries p`.
* `precomposition_dichotomy` is stated for every `k : ℕ`; for `k = 0` the action is constant.
  "Analytic nowhere" is `∀ f₀, ¬ AnalyticAt K _ f₀`.
-/

namespace AlternatingAnalyticChallenge.Prop3_3

/-- A continuous polynomial: a finite sum of diagonals of bounded multilinear maps. -/
def IsContinuousPolynomial (K : Type*) [NontriviallyNormedField K]
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace K X]
    [NormedAddCommGroup Y] [NormedSpace K Y] (g : X → Y) : Prop :=
  ∃ (p : FormalMultilinearSeries K X Y) (N : ℕ),
    ∀ x, g x = ∑ n ∈ Finset.range N, p n (fun _ => x)

/-- Conditions (1), (2) and (3) are equivalent. -/
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
  sorry

/-- Each precomposition action is either a continuous
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
  sorry

end AlternatingAnalyticChallenge.Prop3_3
