import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import AlternatingAnalytic.Analysis.SphericalCompleteness

/-!
# Theorem 4.2 (spherically complete targets), pp. 9-10

Paper statement (Section 4.1, `thm:spherical`): Suppose `K` is nonarchimedean and `F` is
nonarchimedean and spherically complete. Then, for every normed `E`, the space `Alt^k(E;F)` is
nonarchimedean and spherically complete, and its inclusion into `Mult^k(E;F)` has a contractive
linear retraction. Thus `A^k_{E,E';F}` is a continuous polynomial for every normed `E, E'` and
every `k`. Neither the field nor the source spaces need be complete.

A normed space is *spherically complete* if every nonempty family of pairwise-intersecting closed
balls has a common point (p. 9). A *continuous polynomial* is a finite sum of diagonals of
bounded multilinear maps (p. 8). `A^k_{E,E';F}(f)(m) = m ∘ (f, …, f)` is precomposition.

## Formalization notes
* Degree: the index type is `Fin k`, every `k : ℕ` (including `0`).
* `K` is a `NontriviallyNormedField` with `IsUltrametricDist K`; `F` is a normed `K`-space with
  `IsUltrametricDist F` and `SphericallyCompleteSpace F`. `E, E'` are arbitrary normed spaces
  (norms not assumed ultrametric). No completeness anywhere.
* `SphericallyCompleteSpace` is the library class from
  `AlternatingAnalytic.Analysis.SphericalCompleteness` (imported only for this definition; it is
  literally "every nonempty family of pairwise-meeting closed balls has a common point"). That
  module also contains the `IsUltrametricDist` instance for alternating-map spaces, so the
  ultrametric part (`part1_ultrametric`) is an instance already visible here; the spherical
  completeness instance lives in a module that is not imported.
* "Nonarchimedean" for a normed space is Mathlib's `IsUltrametricDist`.
* Contractive linear retraction: a continuous linear `r : Mult^k(E;F) →L[K] Alt^k(E;F)` with
  `‖r‖ ≤ 1` and `r (j m) = m`, where `j = toContinuousMultilinearMap`.
* `IsContinuousPolynomial` (introduced here) formalizes "finite sum of diagonals of bounded
  multilinear maps": `f x = ∑_{i < N} P_i (x, …, x)` with each `P_i` a continuous multilinear map
  of some arity `deg i`.
* The library proves a stronger form of part 3: a single bounded `k`-linear lift of `A^k`
  (one homogeneous diagonal, `N = 1`, degree `k`), which is what the paper's proof gives via
  Proposition 4.1. The challenge states only the paper's weaker wording.
* The theorem is split into `part1_ultrametric`, `part1_sphericallyComplete`,
  `part2_retraction` and `part3_continuousPolynomial`.
-/

namespace AlternatingAnalyticChallenge.Thm4_2

universe uK uE uE' uF uX uY

/-- A map is a *continuous polynomial* if it is a finite sum of diagonals of bounded
multilinear maps. -/
def IsContinuousPolynomial (K : Type uK) [NontriviallyNormedField K]
    {X : Type uX} {Y : Type uY} [NormedAddCommGroup X] [NormedSpace K X]
    [NormedAddCommGroup Y] [NormedSpace K Y] (f : X → Y) : Prop :=
  ∃ (N : ℕ) (deg : Fin N → ℕ)
    (P : ∀ i : Fin N, ContinuousMultilinearMap K (fun _ : Fin (deg i) => X) Y),
    ∀ x, f x = ∑ i, P i (fun _ => x)

/-- **Theorem 4.2, nonarchimedean part.** `Alt^k(E;F)` is nonarchimedean. -/
theorem part1_ultrametric
    (K : Type uK) [NontriviallyNormedField K] [IsUltrametricDist K]
    (E : Type uE) (F : Type uF)
    [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup F] [NormedSpace K F] [IsUltrametricDist F] [SphericallyCompleteSpace F]
    (k : ℕ) :
    IsUltrametricDist (E [⋀^Fin k]→L[K] F) := by
  sorry

/-- **Theorem 4.2, spherical completeness.** `Alt^k(E;F)` is spherically complete. -/
theorem part1_sphericallyComplete
    (K : Type uK) [NontriviallyNormedField K] [IsUltrametricDist K]
    (E : Type uE) (F : Type uF)
    [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup F] [NormedSpace K F] [IsUltrametricDist F] [SphericallyCompleteSpace F]
    (k : ℕ) :
    SphericallyCompleteSpace (E [⋀^Fin k]→L[K] F) := by
  sorry

/-- **Theorem 4.2, retraction.** The inclusion `Alt^k(E;F) ↪ Mult^k(E;F)` has a contractive
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

/-- **Theorem 4.2, polynomiality.** Precomposition `A^k_{E,E';F}` is a continuous polynomial,
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
