import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import AlternatingAnalytic.Analysis.SphericalCompleteness

/-!
# Theorem 4.2 (spherically complete targets), pp. 9-10

Paper statement (Section 4.1): "Suppose `K` is nonarchimedean and `F` is nonarchimedean and
spherically complete. Then, for every normed `E`, the space `Alt^k(E;F)` is nonarchimedean and
spherically complete, and its inclusion into `Mult^k(E;F)` has a contractive linear retraction.
Thus `A^k_{E,E';F}` is a continuous polynomial for every normed `E, E'` and every `k`. Neither
the field nor the source spaces need be complete."

A normed space is spherically complete if every nonempty family of pairwise-intersecting closed
balls has a common point (p. 9). A continuous polynomial is a finite sum of diagonals of
bounded multilinear maps (p. 8). `A^k_{E,E';F}(f)(m) = m ∘ (f, …, f)` is precomposition.

## Formalization notes
* `k : ℕ` is arbitrary, including `0`.
* "Nonarchimedean" is Mathlib's `IsUltrametricDist`. The norms of `E, E'` need not be ultrametric.
* `SphericallyCompleteSpace` is imported from `AlternatingAnalytic.Analysis.SphericalCompleteness`
  for its definition. That module also has the `IsUltrametricDist` instance on alternating maps,
  so `part1_ultrametric` holds by instance search here.
* A contractive retraction is `r : Mult^k(E;F) →L[K] Alt^k(E;F)` with `‖r‖ ≤ 1` and
  `r (j m) = m`, where `j = toContinuousMultilinearMap`.
* `IsContinuousPolynomial f` says `f x = ∑_{i < N} P_i (x, …, x)` with each `P_i` a continuous
  multilinear map of arity `deg i`.
* Part 3 states the paper's wording. The proof gives more: a single homogeneous diagonal of
  degree `k`.
-/

namespace AlternatingAnalyticChallenge.Thm4_2

universe uK uE uE' uF uX uY

/-- A map is a continuous polynomial if it is a finite sum of diagonals of bounded
multilinear maps. -/
def IsContinuousPolynomial (K : Type uK) [NontriviallyNormedField K]
    {X : Type uX} {Y : Type uY} [NormedAddCommGroup X] [NormedSpace K X]
    [NormedAddCommGroup Y] [NormedSpace K Y] (f : X → Y) : Prop :=
  ∃ (N : ℕ) (deg : Fin N → ℕ)
    (P : ∀ i : Fin N, ContinuousMultilinearMap K (fun _ : Fin (deg i) => X) Y),
    ∀ x, f x = ∑ i, P i (fun _ => x)

/-- `Alt^k(E;F)` is nonarchimedean. -/
theorem part1_ultrametric
    (K : Type uK) [NontriviallyNormedField K] [IsUltrametricDist K]
    (E : Type uE) (F : Type uF)
    [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup F] [NormedSpace K F] [IsUltrametricDist F] [SphericallyCompleteSpace F]
    (k : ℕ) :
    IsUltrametricDist (E [⋀^Fin k]→L[K] F) := by
  sorry

/-- `Alt^k(E;F)` is spherically complete. -/
theorem part1_sphericallyComplete
    (K : Type uK) [NontriviallyNormedField K] [IsUltrametricDist K]
    (E : Type uE) (F : Type uF)
    [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup F] [NormedSpace K F] [IsUltrametricDist F] [SphericallyCompleteSpace F]
    (k : ℕ) :
    SphericallyCompleteSpace (E [⋀^Fin k]→L[K] F) := by
  sorry

/-- The inclusion `Alt^k(E;F) ↪ Mult^k(E;F)` has a contractive
continuous linear retraction. -/
theorem part2_retraction
    (K : Type uK) [NontriviallyNormedField K] [IsUltrametricDist K]
    (E : Type uE) (F : Type uF)
    [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup F] [NormedSpace K F] [IsUltrametricDist F] [SphericallyCompleteSpace F]
    (k : ℕ) :
    ∃ r : (E [×k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F),
      ‖r‖ ≤ 1 ∧ ∀ m : E [⋀^Fin k]→L[K] F, r m.toContinuousMultilinearMap = m := by
  sorry

/-- Precomposition `A^k_{E,E';F}` is a continuous polynomial,
for all normed `E, E'` and every `k`. -/
theorem part3_continuousPolynomial
    (K : Type uK) [NontriviallyNormedField K] [IsUltrametricDist K]
    (E : Type uE) (E' : Type uE') (F : Type uF)
    [NormedAddCommGroup E] [NormedSpace K E] [NormedAddCommGroup E'] [NormedSpace K E']
    [NormedAddCommGroup F] [NormedSpace K F] [IsUltrametricDist F] [SphericallyCompleteSpace F]
    (k : ℕ) :
    IsContinuousPolynomial K
      (fun f : E →L[K] E' =>
        (ContinuousAlternatingMap.compContinuousLinearMapCLM f :
          (E' [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F))) := by
  sorry

end AlternatingAnalyticChallenge.Thm4_2
