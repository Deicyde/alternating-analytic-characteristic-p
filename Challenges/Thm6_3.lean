import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Data.Nat.Factorial.Basic
import AlternatingAnalytic.Analysis.SphericalCompleteness

/-!
# Theorem 6.3 (universal scalar classification), p. 16

Paper statement: "Let K be a complete nonarchimedean, nontrivially normed field. For any
k ≥ 0, the contravariant functor Alt^k(−; K) : Vec_K^op → Vec_K is analytic on every Hom space
if and only if k! ≠ 0 in K or K is spherically complete. The same equivalence holds when the
source category is restricted to Banach spaces, or to nonarchimedean Banach spaces."

On the Hom space `Hom_{Vec^op}(D, E) = L(E, D)` the functor acts by
`A^k_{E,D;K}(u) = u^* : Alt^k(D; K) → Alt^k(E; K)`, `m ↦ m ∘ (u, …, u)`.

## Formalization notes
* The degree is `Fin k`; `k! ≠ 0 in K` is `(k.factorial : K) ≠ 0`.
* "Complete nonarchimedean" is `[CompleteSpace K] [IsUltrametricDist K]`. "Spherically
  complete" is the library class `SphericallyCompleteSpace K` (every nonempty family of
  pairwise-meeting closed balls has a common point).
* "Analytic on every Hom space" is `AnalyticOnNhd K A^k_{E,D;K} Set.univ` for all spaces in the
  universe of `K`.
* The paper's "analytic" means the class `C^ω`; the power-series form is stated here. The two
  agree in this case: the positive directions give `CPolynomialAt`, and the negative direction
  gives failure of `AnalyticAt`, which rules out `C^ω`.
* The functor is stated in hom coordinates via
  `ContinuousAlternatingMap.compContinuousLinearMapCLM`; functoriality is not restated.
* The three source categories are all normed spaces, Banach spaces (`CompleteSpace`), and
  nonarchimedean Banach spaces (`CompleteSpace` and `IsUltrametricDist`).
* `analyticOnNhd_of_factorial_ne_zero_or_sphericallyComplete` is the "if" direction for
  arbitrary normed sources; it gives the "if" direction of all three equivalences.
-/

namespace AlternatingAnalyticChallenge.Thm6_3

universe u

/-- Theorem 6.3, "if" direction: if `k! ≠ 0` in `K` or `K` is spherically complete, the
pullback `u ↦ u^*` on `Alt^k(−; K)` is analytic on every Hom space. -/
theorem analyticOnNhd_of_factorial_ne_zero_or_sphericallyComplete
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] (k : ℕ)
    (h : (k.factorial : K) ≠ 0 ∨ SphericallyCompleteSpace K)
    (E D : Type u) [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup D] [NormedSpace K D] :
    AnalyticOnNhd K
      (fun u : E →L[K] D =>
        (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
          (D [⋀^Fin k]→L[K] K) →L[K] (E [⋀^Fin k]→L[K] K))) Set.univ := by
  sorry

/-- Theorem 6.3, normed sources: `Alt^k(−; K)` on `Vec_K^op` is analytic on every Hom space
if and only if `k! ≠ 0` in `K` or `K` is spherically complete. -/
theorem analytic_on_homs_iff
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] (k : ℕ) :
    (∀ (E D : Type u) [NormedAddCommGroup E] [NormedSpace K E]
      [NormedAddCommGroup D] [NormedSpace K D],
      AnalyticOnNhd K
        (fun u : E →L[K] D =>
          (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
            (D [⋀^Fin k]→L[K] K) →L[K] (E [⋀^Fin k]→L[K] K))) Set.univ) ↔
    ((k.factorial : K) ≠ 0 ∨ SphericallyCompleteSpace K) := by
  sorry

/-- Theorem 6.3, Banach sources: the same equivalence for Banach source spaces. -/
theorem analytic_on_homs_iff_banach
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] (k : ℕ) :
    (∀ (E D : Type u) [NormedAddCommGroup E] [NormedSpace K E] [CompleteSpace E]
      [NormedAddCommGroup D] [NormedSpace K D] [CompleteSpace D],
      AnalyticOnNhd K
        (fun u : E →L[K] D =>
          (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
            (D [⋀^Fin k]→L[K] K) →L[K] (E [⋀^Fin k]→L[K] K))) Set.univ) ↔
    ((k.factorial : K) ≠ 0 ∨ SphericallyCompleteSpace K) := by
  sorry

/-- Theorem 6.3, nonarchimedean Banach sources: the same equivalence for nonarchimedean
Banach source spaces. -/
theorem analytic_on_homs_iff_nonarchimedean_banach
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] (k : ℕ) :
    (∀ (E D : Type u) [NormedAddCommGroup E] [NormedSpace K E] [CompleteSpace E]
      [IsUltrametricDist E] [NormedAddCommGroup D] [NormedSpace K D] [CompleteSpace D]
      [IsUltrametricDist D],
      AnalyticOnNhd K
        (fun u : E →L[K] D =>
          (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
            (D [⋀^Fin k]→L[K] K) →L[K] (E [⋀^Fin k]→L[K] K))) Set.univ) ↔
    ((k.factorial : K) ≠ 0 ∨ SphericallyCompleteSpace K) := by
  sorry

end AlternatingAnalyticChallenge.Thm6_3
