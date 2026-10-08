import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Within

/-!
# Theorem 4.5(2) (summable parameter spaces: ℓ¹), p. 11

Paper statement (Section 4.2, `thm:summable-parameters`, part (2)): Let `j : W → Z` be a closed
linear isometry. Suppose `Z` is complete. Let `a : H → W` have an ambient bounded homogeneous
polynomial representation of fixed degree `d`. For every analytic `γ : U → H`, with
`U ⊆ ℓ¹(I, K)` open, the composite `a γ` is analytic. Here `ℓ¹` carries the ordinary sum norm.
The field need not be complete. Each assertion remains valid for a parameter space that is a
bounded linear retract of the indicated space. (The proof continues on p. 12.)

## Formalization notes
* `ℓ¹(I, K)` is Mathlib's `lp (fun _ : I => K) 1` for an arbitrary index type `I` (the library
  abbreviation `L1 K I` is definitionally this space).
* "Ambient bounded homogeneous polynomial representation of fixed degree `d`" is a bounded
  `d`-linear map `B : ContinuousMultilinearMap K (fun _ : Fin d => H) Z` with
  `j (a h) = B (h, …, h)` for all `h : H` (as in the paper's proof and in the remark after the
  theorem). Degree `d = 0` is included.
* A closed linear isometry is `j : W →ₗᵢ[K] Z` with `IsClosed (Set.range j)`.
* `γ : U → H` is modelled as a total map with `AnalyticOn K γ U` on the open set `U`;
  the conclusion is `AnalyticOn K (a ∘ γ) U`.
* The retract clause: `P` normed, `i : P →L[K] ℓ¹(I, K)`, `r : ℓ¹(I, K) →L[K] P`,
  `r ∘ i = id`.
* No completeness of `K`, `H`, `W` or `P`; no characteristic or ultrametric hypotheses.
-/

namespace AlternatingAnalyticChallenge.Thm4_5b

universe uI uK uH uW uZ uP

/-- **Theorem 4.5(2).** `Z` complete, `j : W → Z` a closed linear isometry, and `a : H → W`
with an ambient bounded homogeneous polynomial representation of fixed degree `d`
(`j (a h) = B (h, …, h)` for a bounded `d`-linear `B : H^d → Z`). For every `γ : U → H`
analytic on an open `U ⊆ ℓ¹(I, K)`, the composite `a ∘ γ` is analytic on `U`. -/
theorem l1_analyticOn_comp_of_fixed_degree_representation
    {I : Type uI} {K : Type uK} [NontriviallyNormedField K]
    {H : Type uH} [NormedAddCommGroup H] [NormedSpace K H]
    {W : Type uW} [NormedAddCommGroup W] [NormedSpace K W]
    {Z : Type uZ} [NormedAddCommGroup Z] [NormedSpace K Z] [CompleteSpace Z]
    (j : W →ₗᵢ[K] Z) (hj : IsClosed (Set.range j)) (d : ℕ)
    (B : ContinuousMultilinearMap K (fun _ : Fin d => H) Z)
    (a : H → W) (ha : ∀ h, j (a h) = B (fun _ => h))
    {U : Set (lp (fun _ : I => K) 1)} (hU : IsOpen U)
    {γ : lp (fun _ : I => K) 1 → H} (hγ : AnalyticOn K γ U) :
    AnalyticOn K (a ∘ γ) U := by
  sorry

/-- **Theorem 4.5(2), bounded linear retract clause.** The same conclusion for a parameter
space `P` that is a bounded linear retract of `ℓ¹(I, K)`: `i : P → ℓ¹(I, K)` and
`r : ℓ¹(I, K) → P` bounded linear with `r ∘ i = id_P`. -/
theorem l1_retract_analyticOn_comp_of_fixed_degree_representation
    {I : Type uI} {K : Type uK} [NontriviallyNormedField K]
    {H : Type uH} [NormedAddCommGroup H] [NormedSpace K H]
    {W : Type uW} [NormedAddCommGroup W] [NormedSpace K W]
    {Z : Type uZ} [NormedAddCommGroup Z] [NormedSpace K Z] [CompleteSpace Z]
    {P : Type uP} [NormedAddCommGroup P] [NormedSpace K P]
    (i : P →L[K] lp (fun _ : I => K) 1) (r : lp (fun _ : I => K) 1 →L[K] P)
    (hri : r.comp i = ContinuousLinearMap.id K P)
    (j : W →ₗᵢ[K] Z) (hj : IsClosed (Set.range j)) (d : ℕ)
    (B : ContinuousMultilinearMap K (fun _ : Fin d => H) Z)
    (a : H → W) (ha : ∀ h, j (a h) = B (fun _ => h))
    {U : Set P} (hU : IsOpen U)
    {γ : P → H} (hγ : AnalyticOn K γ U) :
    AnalyticOn K (a ∘ γ) U := by
  sorry

end AlternatingAnalyticChallenge.Thm4_5b
