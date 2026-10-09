import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Analytic.Constructions

/-!
# Proposition 6.4 (shear realization), pp. 16-17

Paper statement (Section 6.1): Suppose `A = A^k_{E,D;F}` is not analytic at `u₀ ∈ L(E, D)`.
Set `H = D ⊕ E`, with the maximum norm, and `g(u)(d, e) = (d + u e, e)`. Both `g` and its
inverse family are affine analytic. Nevertheless, the family of pullback operators `g(u)^*` on
`Alt^k(H; F)` is not analytic at `u₀`.

Here `A^k_{E,D;F} : L(E, D) → L(Alt^k(D;F), Alt^k(E;F))`, `A(u)(m) = m ∘ (u, …, u)`, and
`K` is a nontrivially normed field, `D, E, F` normed `K`-spaces.

## Formalization notes
* The degree is `Fin k`.
* `H = D ⊕ E` is the product `D × E`, whose Mathlib norm is the maximum norm.
* `Alt^k(X;F)` is `X [⋀^Fin k]→L[K] F`; pullback is
  `ContinuousAlternatingMap.compContinuousLinearMapCLM`.
* `shear u = id + shearLinear u`, so `shear u (d, e) = (d + u e, e)`.
* "Affine analytic" means: the family is `id + L u` for a bounded linear map
  `L : L(E,D) →L L(H,H)`, and it is `AnalyticOnNhd` on all of `L(E, D)`.
* "Its inverse family" is a family `ginv` that is a two-sided inverse of `shear u` for every
  `u` and is itself affine analytic.
* The three assertions are `part1`, `part2` and `part3`. The bundle realization after the
  proposition is in `Prop6_4_bundle`.
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

/-- Proposition 6.4, part 1: the shear family `g` is affine analytic. -/
theorem part1 (K : Type uK) [NontriviallyNormedField K]
    (D : Type uD) (E : Type uE)
    [NormedAddCommGroup D] [NormedSpace K D] [NormedAddCommGroup E] [NormedSpace K E] :
    (∀ (u : E →L[K] D) (z : D × E), shear u z = (z.1 + u z.2, z.2)) ∧
    (∃ L : (E →L[K] D) →L[K] (D × E →L[K] D × E),
      ∀ u : E →L[K] D, shear u = ContinuousLinearMap.id K (D × E) + L u) ∧
    AnalyticOnNhd K (fun u : E →L[K] D => shear u) Set.univ := by
  sorry

/-- Proposition 6.4, part 2: the inverse family of `g` is affine analytic. -/
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
  sorry

/-- Proposition 6.4, part 3: if `A^k_{E,D;F}` is not analytic at `u₀`, then the family of
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
  sorry

end AlternatingAnalyticChallenge.Prop6_4
