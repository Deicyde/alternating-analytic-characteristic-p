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
* The degree is `Fin k`. "Characteristic `p > 0`" is `p` prime with `[CharP K p]`. "Not
  spherically complete" is `¬ SphericallyCompleteSpace K` (library class). No ultrametric
  hypothesis is needed: a normed field of positive characteristic is nonarchimedean.
* Part 1: the manifold is a Banach space `X` with global charts `id_X` and an equivalence
  `ψ : X ≃ X`, with `ψ` and `ψ⁻¹` analytic on `X`. An abstract manifold with two global charts is
  identified with `X` by the first chart. The transition on `Alt^k(X; K)` at `x` is pullback by
  the chart derivative, `(Dψ(x))^*`; the reverse transition is `(Dψ⁻¹(y))^*`.
* Part 2: "polynomial analytic" is `CPolynomialOn K h univ`. The pulled-back form is
  `x ↦ (ω₀ (h x)).compContinuousLinearMap (fderiv K h x)`, and the inclusion into
  `Mult^k(N; K)` is `ContinuousAlternatingMap.toContinuousMultilinearMap`.
* The witnesses live in the universe of `K`.
-/

namespace AlternatingAnalyticChallenge.Prop6_5

universe u

/-- Proposition 6.5(1): a Banach space `X` with two global analytic charts `id` and `ψ` whose
induced transitions on scalar alternating `k`-forms are analytic at no point. -/
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

/-- Proposition 6.5(2): Banach spaces `N, Y`, a polynomial analytic `h : N → Y` and an
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
