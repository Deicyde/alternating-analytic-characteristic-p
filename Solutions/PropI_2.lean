import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import AlternatingAnalytic.Coordinates.AlgebraicPolynomialCZero.BoundedLift

/-!
# Proposition I.2 (continuous algebraic polynomials on c₀), pp. 62-63

Solution: the statement of `Challenges/PropI_2.lean`, proved by
`AlgebraicPolynomialCZero.exists_boundedLift_of_continuous_algebraicPolynomial`
(`Coordinates/AlgebraicPolynomialCZero/BoundedLift.lean`) with the constant `L ^ n`, where `L`
bounds the inverse Vandermonde matrix of the nodes `1, t, …, tⁿ` (`0 < |t| < 1`). Ingredients:
`sum_interpolation` (`Interpolation.lean`), `sum_smul_coeff` and
`sum_filter_wordCount_eq_coeff` (`SortedWords.lean`), `exists_diag_bound` (`DiagonalNorm.lean`)
and `CZero.boundedArrayMultilinearMap` (`Analysis/CZeroCoordinates.lean`).
-/

open scoped ZeroAtInfty

namespace AlternatingAnalyticChallenge.PropI_2

universe uK uI uZ

/-- The diagonal norm `‖p‖_diag = inf {D ≥ 0 : ‖p x‖ ≤ D ‖x‖^n for all x}` of a map on a
normed space (a real `sInf`; it is the true infimum when the set is nonempty). -/
noncomputable def diagNorm {X : Type uI} {Z : Type uZ} [Norm X] [Norm Z] (n : ℕ)
    (p : X → Z) : ℝ :=
  sInf {D : ℝ | 0 ≤ D ∧ ∀ x, ‖p x‖ ≤ D * ‖x‖ ^ n}

/-- **Proposition I.2.** Over a nonarchimedean field `K` (not necessarily complete) and for
`n ≥ 1`, there is a constant `C` depending only on `K, n` such that every continuous algebraic
homogeneous polynomial `p : c₀(I,K) → Z` of degree `n`, into a complete nonarchimedean `Z`, has
finite diagonal norm and a bounded `n`-linear lift `q` with `‖q‖ ≤ C ‖p‖_diag`. -/
theorem exists_boundedLift_of_continuous_algebraicPolynomial
    (K : Type uK) [NontriviallyNormedField K] [IsUltrametricDist K] (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (I : Type uI) [TopologicalSpace I] [DiscreteTopology I]
        (Z : Type uZ) [NormedAddCommGroup Z] [NormedSpace K Z] [CompleteSpace Z]
        [IsUltrametricDist Z] (p : C₀(I, K) → Z),
        Continuous p →
        (∃ b : MultilinearMap K (fun _ : Fin n => C₀(I, K)) Z, ∀ x, p x = b (fun _ => x)) →
        (∃ D : ℝ, 0 ≤ D ∧ ∀ x, ‖p x‖ ≤ D * ‖x‖ ^ n) ∧
        ∃ q : ContinuousMultilinearMap K (fun _ : Fin n => C₀(I, K)) Z,
          (∀ x, q (fun _ => x) = p x) ∧ ‖q‖ ≤ C * diagNorm n p :=
  AlgebraicPolynomialCZero.exists_boundedLift_of_continuous_algebraicPolynomial K n hn

end AlternatingAnalyticChallenge.PropI_2
