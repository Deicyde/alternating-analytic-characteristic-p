/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
import AlternatingAnalytic.Scalar.ScalarClassification
import AlternatingAnalytic.Scalar.ScalarObstruction
import AlternatingAnalytic.Scalar.ChainSpaces.Unconditional

/-!
# The universal scalar classification, unconditionally (Theorem 6.3)

`ScalarClassification.lean` proves Theorem 6.3 assuming `ScalarObstruction K k`, the conclusion
of Theorem 6.1(2). Over a complete field that hypothesis follows from the Theorem F.1 witnesses
`ChainSpaces.abstractConclusion`, which gives the three equivalences of Theorem 6.3 outright.
-/

namespace AlternatingAnalytic.ScalarClassification

universe u

/-- Theorem 6.1(2) in the form used by Theorem 6.3: over a complete field, `ScalarObstruction K k`
holds in every degree. -/
theorem scalarObstruction (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] (k : ℕ) :
    ScalarObstruction K k := fun p _ hp hpk hK =>
  ScalarObstruction.exists_nonarchimedean_banach_nowhere_analytic_scalar_of_thmF K p k hp hpk hK
    fun hK _ hk => ChainSpaces.abstractConclusion K hK k hk

/-- Theorem 6.3 for normed sources. -/
theorem analytic_on_homs_iff'
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] (k : ℕ) :
    (∀ (E D : Type u) [NormedAddCommGroup E] [NormedSpace K E]
      [NormedAddCommGroup D] [NormedSpace K D],
      AnalyticOnNhd K
        (fun u : E →L[K] D =>
          (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
            (D [⋀^Fin k]→L[K] K) →L[K] (E [⋀^Fin k]→L[K] K))) Set.univ) ↔
    ((k.factorial : K) ≠ 0 ∨ SphericallyCompleteSpace K) :=
  analytic_on_homs_iff K k (scalarObstruction K k)

/-- Theorem 6.3 for Banach sources. -/
theorem analytic_on_homs_iff_banach'
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] (k : ℕ) :
    (∀ (E D : Type u) [NormedAddCommGroup E] [NormedSpace K E] [CompleteSpace E]
      [NormedAddCommGroup D] [NormedSpace K D] [CompleteSpace D],
      AnalyticOnNhd K
        (fun u : E →L[K] D =>
          (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
            (D [⋀^Fin k]→L[K] K) →L[K] (E [⋀^Fin k]→L[K] K))) Set.univ) ↔
    ((k.factorial : K) ≠ 0 ∨ SphericallyCompleteSpace K) :=
  analytic_on_homs_iff_banach K k (scalarObstruction K k)

/-- Theorem 6.3 for nonarchimedean Banach sources. -/
theorem analytic_on_homs_iff_nonarchimedean_banach'
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] (k : ℕ) :
    (∀ (E D : Type u) [NormedAddCommGroup E] [NormedSpace K E] [CompleteSpace E]
      [IsUltrametricDist E] [NormedAddCommGroup D] [NormedSpace K D] [CompleteSpace D]
      [IsUltrametricDist D],
      AnalyticOnNhd K
        (fun u : E →L[K] D =>
          (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
            (D [⋀^Fin k]→L[K] K) →L[K] (E [⋀^Fin k]→L[K] K))) Set.univ) ↔
    ((k.factorial : K) ≠ 0 ∨ SphericallyCompleteSpace K) :=
  analytic_on_homs_iff_nonarchimedean_banach K k (scalarObstruction K k)

end AlternatingAnalytic.ScalarClassification
