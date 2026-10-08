import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Analytic.Constructions
import AlternatingAnalytic.Analysis.ShearCounterexample

/-!
# Proposition 6.4 (shear realization), p. 16

Solution: the statements of `Challenges/Prop6_4.lean`, proved from the library
(`AlternatingAnalytic/Analysis/ShearCounterexample.lean`): `shear_apply`, `analyticAt_shear`,
`shear_neg_apply`, `shear_apply_neg`, `analyticAt_shear_inverse` and
`not_analyticAt_shear_pullback` (the operator part of `invertible_shear_counterexample`).
The local `shearLinear`/`shear` are definitionally the library's.
-/

namespace AlternatingAnalyticChallenge.Prop6_4

universe uK uD uE uF

/-- The bounded linear part `u ↦ ((d, e) ↦ (u e, 0))` of the shear family. -/
noncomputable def shearLinear (K : Type uK) [NontriviallyNormedField K]
    (D : Type uD) (E : Type uE)
    [NormedAddCommGroup D] [NormedSpace K D] [NormedAddCommGroup E] [NormedSpace K E] :
    (E →L[K] D) →L[K] (D × E →L[K] D × E) :=
  ((ContinuousLinearMap.compL K (D × E) E (D × E)).flip
    (ContinuousLinearMap.snd K D E)).comp
    (ContinuousLinearMap.compL K E D (D × E) (ContinuousLinearMap.inl K D E))

/-- The shear `g(u)(d, e) = (d + u e, e)` on `H = D × E`. -/
noncomputable def shear {K : Type uK} [NontriviallyNormedField K]
    {D : Type uD} {E : Type uE}
    [NormedAddCommGroup D] [NormedSpace K D] [NormedAddCommGroup E] [NormedSpace K E]
    (u : E →L[K] D) : D × E →L[K] D × E :=
  ContinuousLinearMap.id K (D × E) + shearLinear K D E u

/-- **Proposition 6.4, part 1.** The shear family `g` is affine analytic. -/
theorem part1 (K : Type uK) [NontriviallyNormedField K]
    (D : Type uD) (E : Type uE)
    [NormedAddCommGroup D] [NormedSpace K D] [NormedAddCommGroup E] [NormedSpace K E] :
    (∀ (u : E →L[K] D) (z : D × E), shear u z = (z.1 + u z.2, z.2)) ∧
    (∃ L : (E →L[K] D) →L[K] (D × E →L[K] D × E),
      ∀ u : E →L[K] D, shear u = ContinuousLinearMap.id K (D × E) + L u) ∧
    AnalyticOnNhd K (fun u : E →L[K] D => shear u) Set.univ := by
  refine ⟨fun u z => AlternatingAnalytic.shear_apply u z, ⟨shearLinear K D E, fun u => rfl⟩,
    fun u _ => AlternatingAnalytic.analyticAt_shear u⟩

/-- **Proposition 6.4, part 2.** The inverse family of `g` is affine analytic. -/
theorem part2 (K : Type uK) [NontriviallyNormedField K]
    (D : Type uD) (E : Type uE)
    [NormedAddCommGroup D] [NormedSpace K D] [NormedAddCommGroup E] [NormedSpace K E] :
    ∃ ginv : (E →L[K] D) → (D × E →L[K] D × E),
      (∀ u : E →L[K] D,
        (ginv u).comp (shear u) = ContinuousLinearMap.id K (D × E) ∧
        (shear u).comp (ginv u) = ContinuousLinearMap.id K (D × E)) ∧
      (∃ L : (E →L[K] D) →L[K] (D × E →L[K] D × E),
        ∀ u : E →L[K] D, ginv u = ContinuousLinearMap.id K (D × E) + L u) ∧
      AnalyticOnNhd K ginv Set.univ := by
  refine ⟨fun u => shear (-u), fun u => ⟨?_, ?_⟩, ⟨-shearLinear K D E, fun u => ?_⟩,
    fun u _ => AlternatingAnalytic.analyticAt_shear_inverse u⟩
  · exact ContinuousLinearMap.ext fun z => AlternatingAnalytic.shear_neg_apply u z
  · exact ContinuousLinearMap.ext fun z => AlternatingAnalytic.shear_apply_neg u z
  · simp [shear]

/-- **Proposition 6.4, part 3.** If `A^k_{E,D;F}` is not analytic at `u₀`, then the family of
pullback operators `g(u)^*` on `Alt^k(D × E; F)` is not analytic at `u₀`. -/
theorem part3 (K : Type uK) [NontriviallyNormedField K]
    (D : Type uD) (E : Type uE) (F : Type uF)
    [NormedAddCommGroup D] [NormedSpace K D] [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup F] [NormedSpace K F] (k : ℕ) (u₀ : E →L[K] D)
    (hA : ¬ AnalyticAt K
      (fun u : E →L[K] D =>
        (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
          (D [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F))) u₀) :
    ¬ AnalyticAt K
      (fun u : E →L[K] D =>
        (ContinuousAlternatingMap.compContinuousLinearMapCLM (shear u) :
          ((D × E) [⋀^Fin k]→L[K] F) →L[K] ((D × E) [⋀^Fin k]→L[K] F))) u₀ := by
  exact AlternatingAnalytic.not_analyticAt_shear_pullback (ι := Fin k) u₀ hA

end AlternatingAnalyticChallenge.Prop6_4
