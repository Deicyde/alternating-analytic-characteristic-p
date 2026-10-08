import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import AlternatingAnalytic.Analysis.SphericalCompleteness
import AlternatingAnalytic.Analysis.SphericalAnalytic

/-!
# Theorem 4.2 (spherically complete targets), pp. 9-10

Solution: the statements of `Challenges/Thm4_2.lean`, proved from the library
(`SphericalCompleteness.lean`, `SphericalAnalytic.lean`, `LiftCriterion.lean`):
* ultrametric: the library `IsUltrametricDist` instance on `E [⋀^ι]→L[𝕜] F`;
* spherical completeness: instance `sphericallyCompleteSpace_continuousAlternatingMap`;
* retraction: `ContinuousAlternatingMap.exists_contracting_retraction_toContinuousMultilinearMap`;
* polynomiality: `ContinuousAlternatingMap.hasBoundedLift_of_sphericallyComplete` with
  `Round24Transfer.hasBoundedLift_iff_exists_ι` (a single homogeneous diagonal).
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
  infer_instance

/-- **Theorem 4.2, spherical completeness.** `Alt^k(E;F)` is spherically complete. -/
theorem part1_sphericallyComplete
    (K : Type uK) [NontriviallyNormedField K] [IsUltrametricDist K]
    (E : Type uE) (F : Type uF)
    [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup F] [NormedSpace K F] [IsUltrametricDist F] [SphericallyCompleteSpace F]
    (k : ℕ) :
    SphericallyCompleteSpace (E [⋀^Fin k]→L[K] F) := by
  infer_instance

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
  exact ContinuousAlternatingMap.exists_contracting_retraction_toContinuousMultilinearMap

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
  obtain ⟨P, hP⟩ := (Round24Transfer.hasBoundedLift_iff_exists_ι).1
    (ContinuousAlternatingMap.hasBoundedLift_of_sphericallyComplete
      (𝕜 := K) (ι := Fin k) (E := E) (E' := E') (F := F))
  exact ⟨1, fun _ => k, fun _ => P, fun f => by simp [hP]⟩

end AlternatingAnalyticChallenge.Thm4_2
