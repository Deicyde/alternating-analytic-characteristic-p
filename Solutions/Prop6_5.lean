import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Analytic.CPolynomialDef
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Algebra.CharP.Defs
import AlternatingAnalytic.Analysis.SphericalCompleteness
import AlternatingAnalytic.Scalar.ScalarObstruction
import AlternatingAnalytic.Scalar.ChainSpaces.Unconditional
import AlternatingAnalytic.Scalar.TangentPullback.Main

/-!
# Proof of Proposition 6.5

Uses Theorem 6.1(2) (`ScalarObstruction.exists_nonarchimedean_banach_nowhere_analytic_scalar_of_thmF`
with `ChainSpaces.abstractConclusion`) and `TangentPullback.tangent_obstruction_of_scalar_obstruction`,
`TangentPullback.pullback_obstruction_of_scalar_obstruction` (`Scalar/TangentPullback/`).
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
  exact AlternatingAnalytic.TangentPullback.tangent_obstruction_of_scalar_obstruction K k
    (AlternatingAnalytic.ScalarObstruction.exists_nonarchimedean_banach_nowhere_analytic_scalar_of_thmF
      K p k hp.pos hpk hK (fun hK _ hk => AlternatingAnalytic.ChainSpaces.abstractConclusion K hK k hk))

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
  exact AlternatingAnalytic.TangentPullback.pullback_obstruction_of_scalar_obstruction K k
    (AlternatingAnalytic.ScalarObstruction.exists_nonarchimedean_banach_nowhere_analytic_scalar_of_thmF
      K p k hp.pos hpk hK (fun hK _ hk => AlternatingAnalytic.ChainSpaces.abstractConclusion K hK k hk))

end AlternatingAnalyticChallenge.Prop6_5
