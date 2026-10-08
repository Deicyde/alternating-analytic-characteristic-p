import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Analytic.CPolynomialDef
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Algebra.CharP.Defs
import AlternatingAnalytic.Analysis.SphericalCompleteness

/-!
# Proposition 6.5 (tangent and pullback obstructions), p. 17

Paper statement (Section 6.2): Suppose `K` is complete, has characteristic `p > 0`, is not
spherically complete, and `k ≥ p`.
1. An analytic Banach manifold has two global analytic charts whose induced transition on scalar
   alternating `k`-forms is analytic at no point.
2. There are Banach spaces `N, Y`, a polynomial analytic map `h : N → Y`, and an analytic map
   `ω₀ : Y → Alt^k(Y; K)` such that `h^* ω₀`, expressed in the product coordinates on `N`, is
   analytic at no point as an `Alt^k(N; K)`-valued map. After inclusion in `Mult^k(N; K)` it is
   analytic everywhere.

## Formalization notes
* Degree: index type `Fin k`. Characteristic: `p` prime with `[CharP K p]` (equivalent to
  "characteristic `p > 0`"). `K` is a `NontriviallyNormedField` with `[CompleteSpace K]` and
  `¬ SphericallyCompleteSpace K`. `SphericallyCompleteSpace` is the library class
  (`AlternatingAnalytic/Analysis/SphericalCompleteness.lean`, imported for this definition only;
  that module does not prove this claim). No ultrametric hypothesis is added (a normed field of
  positive characteristic is automatically nonarchimedean).
* Part 1. The manifold is the Banach space `X` itself; its two global charts are `id_X` and an
  equivalence `ψ : X ≃ X` with `ψ` and `ψ⁻¹` analytic on all of `X` (`AnalyticOnNhd`), i.e. two
  analytically compatible global charts. The induced transition on scalar alternating `k`-forms
  at `x` is pullback by the chart derivative, `x ↦ (Dψ(x))^*` on `Alt^k(X; K)`
  (`ContinuousAlternatingMap.compContinuousLinearMapCLM (fderiv K ψ x)`); the reverse
  transition is `y ↦ (Dψ⁻¹(y))^*`. Both are asserted to be analytic at no point.
  This model-space formulation (rather than an abstract `ChartedSpace`) is a deliberate
  simplification: an abstract manifold with two global charts is identified with `X` by the
  first chart.
* Part 2. "Polynomial analytic" is Mathlib's `CPolynomialOn K h univ`; "analytic" is
  `AnalyticOnNhd K · univ`. The pulled-back form in the global product coordinates of `N` is
  `x ↦ (ω₀ (h x)).compContinuousLinearMap (fderiv K h x)`; the inclusion into `Mult^k(N; K)` is
  `ContinuousAlternatingMap.toContinuousMultilinearMap`.
* The witnesses are asserted to exist in the universe of `K` (the paper does not specify
  universes).
-/

namespace AlternatingAnalyticChallenge.Prop6_5

universe u

/-- **Proposition 6.5(1).** A Banach space `X` (an analytic Banach manifold) with two global
analytic charts `id` and `ψ` whose induced transitions on scalar alternating `k`-forms are
analytic at no point. -/
theorem part1 (K : Type u) [NontriviallyNormedField K] [CompleteSpace K]
    (p k : ℕ) (hp : p.Prime) [CharP K p] (hK : ¬ SphericallyCompleteSpace K) (hpk : p ≤ k) :
    ∃ (X : Type u) (_ : NormedAddCommGroup X) (_ : NormedSpace K X) (_ : CompleteSpace X)
      (ψ : X ≃ X),
      AnalyticOnNhd K ψ Set.univ ∧ AnalyticOnNhd K ψ.symm Set.univ ∧
      (∀ x : X, ¬ AnalyticAt K
        (fun y : X => (ContinuousAlternatingMap.compContinuousLinearMapCLM (fderiv K ψ y) :
          (X [⋀^Fin k]→L[K] K) →L[K] (X [⋀^Fin k]→L[K] K))) x) ∧
      (∀ x : X, ¬ AnalyticAt K
        (fun y : X => (ContinuousAlternatingMap.compContinuousLinearMapCLM (fderiv K ψ.symm y) :
          (X [⋀^Fin k]→L[K] K) →L[K] (X [⋀^Fin k]→L[K] K))) x) := by
  sorry

/-- **Proposition 6.5(2).** Banach spaces `N, Y`, a polynomial analytic `h : N → Y` and an
analytic scalar `k`-form `ω₀` on `Y` whose pullback `h^* ω₀` is analytic at no point as an
`Alt^k(N; K)`-valued map, but is analytic everywhere as a `Mult^k(N; K)`-valued map. -/
theorem part2 (K : Type u) [NontriviallyNormedField K] [CompleteSpace K]
    (p k : ℕ) (hp : p.Prime) [CharP K p] (hK : ¬ SphericallyCompleteSpace K) (hpk : p ≤ k) :
    ∃ (N : Type u) (_ : NormedAddCommGroup N) (_ : NormedSpace K N) (_ : CompleteSpace N)
      (Y : Type u) (_ : NormedAddCommGroup Y) (_ : NormedSpace K Y) (_ : CompleteSpace Y)
      (h : N → Y) (ω₀ : Y → Y [⋀^Fin k]→L[K] K),
      CPolynomialOn K h Set.univ ∧ AnalyticOnNhd K ω₀ Set.univ ∧
      (∀ x : N, ¬ AnalyticAt K
        (fun y : N => (ω₀ (h y)).compContinuousLinearMap (fderiv K h y)) x) ∧
      AnalyticOnNhd K
        (fun y : N => ((ω₀ (h y)).compContinuousLinearMap (fderiv K h y)).toContinuousMultilinearMap)
        Set.univ := by
  sorry

end AlternatingAnalyticChallenge.Prop6_5
