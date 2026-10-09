import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Topology.VectorBundle.ContinuousAlternatingMap
import AlternatingAnalytic.Geometry.ShearBundleGeneral

/-!
# Proof of Proposition 6.4, bundle realization

Uses `shearBundle_realization` (`Geometry/ShearBundleGeneral.lean`), which applies to any vector
bundle core over `E →L[K] D` with shear transitions and two global charts.
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

/-- If `A^k_{E,D;F}` is not analytic at `u₀`, then the shear bundle over `L(E, D)` and the
trivial `F`-bundle are analytic, but the induced atlas of the alternating bundle
`u ↦ Alt^k(H_u; F)` is not analytic. -/
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
      𝓘(K, E →L[K] D) :=
  AlternatingAnalytic.shearBundle_realization k (shearBundleCore K D E)
    (fun i => (AlternatingAnalytic.shearChartWeight i : K)) (fun _ _ _ => rfl) false true rfl rfl
    (by simp [AlternatingAnalytic.shearChartWeight]) u₀ hA

end AlternatingAnalyticChallenge.Prop6_4_bundle
