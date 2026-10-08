import AlternatingAnalytic.Analysis.UniversalAlternatingTargets

/-!
# Universal alternating targets have zero dual

If a universal target `F` of `Alt^k(−; F)` carries a nonzero bounded functional `λ`, choose
`v` with `λ v = 1`; then `c ↦ c • v` and `λ` exhibit the scalar field `K` as a bounded
retract of `F`, so `K` is itself a universal target
(`UniversalAlternatingTarget.of_retract`). Hence, whenever scalar precomposition fails to be
analytic at some point for some pair of spaces (Theorem 6.1(2) of the paper), every universal
target has zero continuous dual (Section 9). The scalar counterexample enters as a hypothesis.
-/

noncomputable section

universe u

namespace AlternatingAnalytic

variable {K : Type u} [NontriviallyNormedField K]

/-- The scalar field is a universal target as soon as some universal target has a nonzero
bounded functional. -/
theorem UniversalAlternatingTarget.scalar_of_ne_zero_dual {k : ℕ} {F : Type u}
    [NormedAddCommGroup F] [NormedSpace K F] (hF : UniversalAlternatingTarget K k F)
    {l : F →L[K] K} (hl : l ≠ 0) : UniversalAlternatingTarget K k K := by
  obtain ⟨w, hw⟩ : ∃ w, l w ≠ 0 := DFunLike.ne_iff.mp hl
  refine hF.of_retract (ContinuousLinearMap.toSpanSingleton K ((l w)⁻¹ • w)) l ?_
  ext
  simp [hw]

/-- If the scalar field is not a universal target, every universal target has zero dual. -/
theorem UniversalAlternatingTarget.dual_eq_zero_of_not_scalar {k : ℕ} {F : Type u}
    [NormedAddCommGroup F] [NormedSpace K F] (hF : UniversalAlternatingTarget K k F)
    (hK : ¬ UniversalAlternatingTarget K k K) (l : F →L[K] K) : l = 0 := by
  by_contra hl
  exact hK (hF.scalar_of_ne_zero_dual hl)

/-- A point where scalar precomposition is not analytic shows that `K` is not a universal
target. -/
theorem not_universalAlternatingTarget_scalar_of_not_analyticAt {k : ℕ} {E D : Type u}
    [NormedAddCommGroup E] [NormedSpace K E] [NormedAddCommGroup D] [NormedSpace K D]
    {u₀ : E →L[K] D}
    (h : ¬ AnalyticAt K
      (fun u : E →L[K] D =>
        (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
          (D [⋀^Fin k]→L[K] K) →L[K] (E [⋀^Fin k]→L[K] K))) u₀) :
    ¬ UniversalAlternatingTarget K k K :=
  fun hK => h (hK E D u₀ (Set.mem_univ u₀))

/-- **Section 9, conditional form.** Given the conclusion of Theorem 6.1(2) (abstract form) for
`K` and `k`, every universal target of `Alt^k(−; F)` has zero continuous dual. -/
theorem UniversalAlternatingTarget.dual_eq_zero_of_scalar_obstruction {k : ℕ}
    (hscalar : ∃ (E D : Type u) (_ : NormedAddCommGroup E) (_ : NormedSpace K E)
      (_ : CompleteSpace E) (_ : IsUltrametricDist E)
      (_ : NormedAddCommGroup D) (_ : NormedSpace K D) (_ : CompleteSpace D)
      (_ : IsUltrametricDist D),
      ∀ u₀ : E →L[K] D,
        ¬ AnalyticAt K
          (fun u : E →L[K] D =>
            (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
              (D [⋀^Fin k]→L[K] K) →L[K] (E [⋀^Fin k]→L[K] K))) u₀)
    {F : Type u} [NormedAddCommGroup F] [NormedSpace K F]
    (hF : UniversalAlternatingTarget K k F) (l : F →L[K] K) : l = 0 := by
  obtain ⟨E, D, _, _, _, _, _, _, _, _, h⟩ := hscalar
  exact hF.dual_eq_zero_of_not_scalar (not_universalAlternatingTarget_scalar_of_not_analyticAt
    (h 0)) l

end AlternatingAnalytic
