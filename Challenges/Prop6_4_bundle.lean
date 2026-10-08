import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Topology.VectorBundle.ContinuousAlternatingMap

/-!
# Proposition 6.4, bundle realization (paragraph after the proposition), p. 16

Paper statement (Section 6.1, after Proposition 6.4): with `A = A^k_{E,D;F}`, `H = D ⊕ E` and
`g(u)(d, e) = (d + u e, e)` as in Proposition 6.4, take the base `M = L(E, D)` and the trivial
bundle `M × H`. Its product trivialization and the trivialization `(u, z) ↦ (u, g(u) z)` form an
analytic bundle atlas. The associated alternating transitions are pullback by `g(u)` and
`g(-u)`. Equation (6.1) proves that this induced atlas fails to be analytic whenever `A` does.
Equivalently, the analytic bundle automorphism `(u, z) ↦ (u, g(u) z)` does not induce an
analytic morphism on the alternating product bundle. (Thus every failure of the Hom-space
criterion has a bundle realization; Theorem 6.1 supplies Banach bases on which this failure
occurs at every point, including the identity operator `g(0)`.)

## Formalization notes
* Degree: index type `Fin k`.
* The two-trivialization bundle `M × H` is encoded as a Mathlib `VectorBundleCore` over
  `M = E →L[K] D` (a manifold with its single identity chart, model `𝓘(K, E →L[K] D)`) with
  fiber `D × E`, two global charts indexed by `Bool`, and transition from chart `i` to chart
  `j` equal to `shear ((w j - w i) • u)` with `w false = 0`, `w true = 1`; so the transition
  `false → true` is `g(u)` and `true → false` is `g(-u)`. This is the library's
  `AlternatingAnalytic.shearBundleCore`, re-declared here (with `shearLinear`, `shear`,
  `shearChartWeight`) using Mathlib only.
* The alternating bundle is Mathlib's bundle `u ↦ Alt^k(H_u; F)` of continuous alternating maps
  from the shear bundle to the trivial bundle `Bundle.Trivial M F`, with Mathlib's induced
  trivializations. "The induced atlas is analytic" is `ContMDiffVectorBundle ω`.
* `bundle_realization` asserts, for arbitrary normed `D, E, F` and any `u₀` at which `A` is not
  analytic: the shear atlas is analytic, the trivial `F`-bundle is analytic, and the induced
  alternating atlas is not analytic.
* Not formalized here: the "equivalently ... does not induce an analytic morphism" reformulation
  and the "failure at every point" sentence (which belongs to Theorem 6.1).
* No completeness or characteristic hypotheses (as in the paper).
-/

open Bundle Set
open scoped Manifold ContDiff

namespace AlternatingAnalyticChallenge.Prop6_4_bundle

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

/-- The parameter weight of the two charts. -/
def shearChartWeight (K : Type uK) [NontriviallyNormedField K] (i : Bool) : K :=
  if i then 1 else 0

/-- The two-chart bundle `M × H` over `M = E →L[K] D`: both charts are global and the
transition from chart `i` to chart `j` is `shear ((w j - w i) • u)`. -/
noncomputable def shearBundleCore (K : Type uK) [NontriviallyNormedField K]
    (D : Type uD) (E : Type uE)
    [NormedAddCommGroup D] [NormedSpace K D] [NormedAddCommGroup E] [NormedSpace K E] :
    VectorBundleCore K (E →L[K] D) (D × E) Bool where
  baseSet _ := univ
  isOpen_baseSet _ := isOpen_univ
  indexAt _ := false
  mem_baseSet_at _ := mem_univ _
  coordChange i j u := shear ((shearChartWeight K j - shearChartWeight K i) • u)
  coordChange_self i u _ v := by
    simp [shear, shearLinear]
  continuousOn_coordChange i j :=
    (continuous_const.add
      ((shearLinear K D E).continuous.comp (continuous_const_smul _))).continuousOn
  coordChange_comp i j k u _ v := by
    ext
    · simp only [shear, shearLinear, add_apply, ContinuousLinearMap.coe_comp,
        Function.comp_apply, ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply,
        ContinuousLinearMap.id_apply, ContinuousLinearMap.coe_snd', ContinuousLinearMap.inl_apply,
        Prod.fst_add, Prod.snd_add, add_zero, FunLike.coe_smul, Pi.smul_apply]
      rw [add_assoc, ← add_smul]
      congr 3
      ring
    · simp [shear, shearLinear]

/-- **Bundle realization of Proposition 6.4.** If `A^k_{E,D;F}` is not analytic at `u₀`, then
the two-trivialization shear bundle over `L(E, D)` and the trivial `F`-bundle are analytic,
but the induced atlas of the alternating bundle `u ↦ Alt^k(H_u; F)` is not analytic. -/
theorem bundle_realization (K : Type uK) [NontriviallyNormedField K]
    (D : Type uD) (E : Type uE) (F : Type uF)
    [NormedAddCommGroup D] [NormedSpace K D] [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup F] [NormedSpace K F] (k : ℕ) (u₀ : E →L[K] D)
    (hA : ¬ AnalyticAt K
      (fun u : E →L[K] D =>
        (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
          (D [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F))) u₀) :
    ContMDiffVectorBundle ω (D × E) (shearBundleCore K D E).Fiber 𝓘(K, E →L[K] D) ∧
    ContMDiffVectorBundle ω F (Bundle.Trivial (E →L[K] D) F) 𝓘(K, E →L[K] D) ∧
    ¬ ContMDiffVectorBundle ω ((D × E) [⋀^Fin k]→L[K] F)
      (fun u ↦ (shearBundleCore K D E).Fiber u [⋀^Fin k]→L[K] Bundle.Trivial (E →L[K] D) F u)
      𝓘(K, E →L[K] D) := by
  sorry

end AlternatingAnalyticChallenge.Prop6_4_bundle
