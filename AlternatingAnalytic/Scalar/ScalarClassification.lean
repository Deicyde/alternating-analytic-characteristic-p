/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
import AlternatingAnalytic.Analysis.FactorialInvertible
import AlternatingAnalytic.Analysis.SphericalAnalytic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.Nat.Prime.Factorial

/-!
# The universal scalar classification (Theorem 6.3)

For a complete nonarchimedean nontrivially normed field `K` and a degree `k`, scalar pullback
`u ↦ u^*` on `Alt^k(−; K)` is analytic on every Hom space if and only if `k! ≠ 0` in `K` or `K` is
spherically complete; the same holds for Banach and for nonarchimedean Banach sources. The "if"
direction combines the case `k! ≠ 0` (`FactorialInvertible.lean`) with Theorem 4.2
(`SphericalAnalytic.lean`). The "only if" direction is proved here assuming the conclusion of
Theorem 6.1(2), stated as `ScalarObstruction K k`; `ScalarClassification/Unconditional.lean`
removes this hypothesis.
-/

open scoped Nat

namespace AlternatingAnalytic.ScalarClassification

universe u

/-- Nonarchimedean Banach spaces `E`, `D` over `K` for which scalar pullback on `Alt^k` is
analytic at no point of `L(E, D)`. -/
def NowhereAnalyticScalarWitness (K : Type u) [NontriviallyNormedField K] (k : ℕ) : Prop :=
  ∃ (E D : Type u) (_ : NormedAddCommGroup E) (_ : NormedSpace K E) (_ : CompleteSpace E)
    (_ : IsUltrametricDist E)
    (_ : NormedAddCommGroup D) (_ : NormedSpace K D) (_ : CompleteSpace D)
    (_ : IsUltrametricDist D),
    ∀ u₀ : E →L[K] D,
      ¬ AnalyticAt K
        (fun u : E →L[K] D =>
          (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
            (D [⋀^Fin k]→L[K] K) →L[K] (E [⋀^Fin k]→L[K] K))) u₀

/-- The conclusion of Theorem 6.1(2) for `K` in degree `k`: in characteristic `p` with
`0 < p ≤ k`, a non-spherically complete `K` has nowhere-analytic witnesses. -/
def ScalarObstruction (K : Type u) [NontriviallyNormedField K] (k : ℕ) : Prop :=
  ∀ (p : ℕ) [CharP K p], 0 < p → p ≤ k → ¬ SphericallyCompleteSpace K →
    NowhereAnalyticScalarWitness K k

/-- If `k! = 0` in a field `K`, then `K` has prime characteristic `p ≤ k`. -/
theorem exists_charP_le_of_factorial_eq_zero {K : Type*} [Field K] {k : ℕ}
    (h : (k ! : K) = 0) : ∃ p, CharP K p ∧ p.Prime ∧ p ≤ k := by
  obtain ⟨p, hp⟩ := CharP.exists K
  have hdvd : p ∣ k ! := (CharP.cast_eq_zero_iff K p _).1 h
  rcases CharP.char_is_prime_or_zero K p with hprime | rfl
  · exact ⟨p, hp, hprime, (Nat.Prime.dvd_factorial hprime).1 hdvd⟩
  · exact absurd (Nat.eq_zero_of_zero_dvd hdvd) (Nat.factorial_ne_zero k)

/-- Theorem 6.3, "if" direction: if `k! ≠ 0` in `K` or `K` is spherically complete, scalar
pullback on `Alt^k(−; K)` is analytic on every Hom space between normed spaces. -/
theorem analyticOnNhd_of_factorial_ne_zero_or_sphericallyComplete
    (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] (k : ℕ)
    (h : (k.factorial : K) ≠ 0 ∨ SphericallyCompleteSpace K)
    (E D : Type u) [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup D] [NormedSpace K D] :
    AnalyticOnNhd K
      (fun u : E →L[K] D =>
        (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
          (D [⋀^Fin k]→L[K] K) →L[K] (E [⋀^Fin k]→L[K] K))) Set.univ := by
  rcases h with h | h
  · refine ContinuousAlternatingMap.analyticOnNhd_compContinuousLinearMapCLM ?_ _
    rwa [Fintype.card_fin]
  · exact fun u₀ _ =>
      ContinuousAlternatingMap.analyticAt_compContinuousLinearMapCLM_of_sphericallyComplete u₀

/-- A nowhere-analytic witness contradicts analyticity on every nonarchimedean Banach Hom space. -/
theorem not_analytic_of_witness (K : Type u) [NontriviallyNormedField K] (k : ℕ)
    (hw : NowhereAnalyticScalarWitness K k)
    (H : ∀ (E D : Type u) [NormedAddCommGroup E] [NormedSpace K E] [CompleteSpace E]
      [IsUltrametricDist E] [NormedAddCommGroup D] [NormedSpace K D] [CompleteSpace D]
      [IsUltrametricDist D],
      AnalyticOnNhd K
        (fun u : E →L[K] D =>
          (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
            (D [⋀^Fin k]→L[K] K) →L[K] (E [⋀^Fin k]→L[K] K))) Set.univ) : False := by
  obtain ⟨E, D, _, _, _, _, _, _, _, _, hE⟩ := hw
  exact hE 0 (H E D 0 (Set.mem_univ _))

/-- Assuming the conclusion of Theorem 6.1(2), analyticity on every nonarchimedean Banach Hom
space forces `k! ≠ 0` in `K` or spherical completeness of `K`. -/
theorem factorial_ne_zero_or_sphericallyComplete_of_analytic
    (K : Type u) [NontriviallyNormedField K] (k : ℕ) (hobs : ScalarObstruction K k)
    (H : ∀ (E D : Type u) [NormedAddCommGroup E] [NormedSpace K E] [CompleteSpace E]
      [IsUltrametricDist E] [NormedAddCommGroup D] [NormedSpace K D] [CompleteSpace D]
      [IsUltrametricDist D],
      AnalyticOnNhd K
        (fun u : E →L[K] D =>
          (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
            (D [⋀^Fin k]→L[K] K) →L[K] (E [⋀^Fin k]→L[K] K))) Set.univ) :
    (k.factorial : K) ≠ 0 ∨ SphericallyCompleteSpace K := by
  by_contra hne
  obtain ⟨hk, hK⟩ := not_or.1 hne
  obtain ⟨p, hp, hprime, hpk⟩ := exists_charP_le_of_factorial_eq_zero (not_not.1 hk)
  exact not_analytic_of_witness K k (hobs p hprime.pos hpk hK) H

/-- Theorem 6.3 for normed sources, assuming the conclusion of Theorem 6.1(2). -/
theorem analytic_on_homs_iff
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] (k : ℕ)
    (hobs : ScalarObstruction K k) :
    (∀ (E D : Type u) [NormedAddCommGroup E] [NormedSpace K E]
      [NormedAddCommGroup D] [NormedSpace K D],
      AnalyticOnNhd K
        (fun u : E →L[K] D =>
          (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
            (D [⋀^Fin k]→L[K] K) →L[K] (E [⋀^Fin k]→L[K] K))) Set.univ) ↔
    ((k.factorial : K) ≠ 0 ∨ SphericallyCompleteSpace K) :=
  ⟨fun H => factorial_ne_zero_or_sphericallyComplete_of_analytic K k hobs fun E D _ _ _ _ _ _ _ _ =>
      H E D,
    fun h E D _ _ _ _ => analyticOnNhd_of_factorial_ne_zero_or_sphericallyComplete K k h E D⟩

/-- Theorem 6.3 for Banach sources, assuming the conclusion of Theorem 6.1(2). -/
theorem analytic_on_homs_iff_banach
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] (k : ℕ)
    (hobs : ScalarObstruction K k) :
    (∀ (E D : Type u) [NormedAddCommGroup E] [NormedSpace K E] [CompleteSpace E]
      [NormedAddCommGroup D] [NormedSpace K D] [CompleteSpace D],
      AnalyticOnNhd K
        (fun u : E →L[K] D =>
          (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
            (D [⋀^Fin k]→L[K] K) →L[K] (E [⋀^Fin k]→L[K] K))) Set.univ) ↔
    ((k.factorial : K) ≠ 0 ∨ SphericallyCompleteSpace K) :=
  ⟨fun H => factorial_ne_zero_or_sphericallyComplete_of_analytic K k hobs fun E D _ _ _ _ _ _ _ _ =>
      H E D,
    fun h E D _ _ _ _ _ _ => analyticOnNhd_of_factorial_ne_zero_or_sphericallyComplete K k h E D⟩

/-- Theorem 6.3 for nonarchimedean Banach sources, assuming the conclusion of
Theorem 6.1(2). -/
theorem analytic_on_homs_iff_nonarchimedean_banach
    (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] (k : ℕ)
    (hobs : ScalarObstruction K k) :
    (∀ (E D : Type u) [NormedAddCommGroup E] [NormedSpace K E] [CompleteSpace E]
      [IsUltrametricDist E] [NormedAddCommGroup D] [NormedSpace K D] [CompleteSpace D]
      [IsUltrametricDist D],
      AnalyticOnNhd K
        (fun u : E →L[K] D =>
          (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
            (D [⋀^Fin k]→L[K] K) →L[K] (E [⋀^Fin k]→L[K] K))) Set.univ) ↔
    ((k.factorial : K) ≠ 0 ∨ SphericallyCompleteSpace K) :=
  ⟨factorial_ne_zero_or_sphericallyComplete_of_analytic K k hobs,
    fun h E D _ _ _ _ _ _ _ _ =>
      analyticOnNhd_of_factorial_ne_zero_or_sphericallyComplete K k h E D⟩

end AlternatingAnalytic.ScalarClassification
