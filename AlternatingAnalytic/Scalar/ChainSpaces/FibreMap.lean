import AlternatingAnalytic.Scalar.ChainSpaces.Operators
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The fibre maps `π_i`

Let `P` be a bounded `k`-linear map `L(E, E')^k → L(Alt^k(E'; K), Alt^k(E; K))` between the
chain-limit spaces `E = chainSpace ρ`, `E' = chainSpace ρ'`, and let `δ` be a continuous
alternating `k`-form on `V'`. For a word `i` the fibre value
`π_i(g¹, …, gᵏ)(ξ₁, …, ξ_k) = P(g¹_{[i]}, …, gᵏ_{[i]})(δ'_i)(ξ_{1[i]}, …, ξ_{k[i]})` (F.8)
is `k`-linear in the maps and alternating in the vectors; `fibreMap` packages it as a
`k`-linear map from `Hom(V, V')^k` (algebraic linear maps; `V` is finite-dimensional) to
algebraic alternating forms on `V`. If `P` lifts the precomposition action, then
`π_i(g, …, g) = δ ∘ (g, …, g)` for every `g` (F.9, `fibreMap_diag`).
-/

open Filter Topology
open scoped ENNReal

set_option maxSynthPendingDepth 2

namespace AlternatingAnalytic.ChainSpaces

variable {K : Type*} [NontriviallyNormedField K] {L : Type*} [DecidableEq L]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace K V]
  {V' : Type*} [NormedAddCommGroup V'] [NormedSpace K V']
  (ρ : L → V →L[K] V) (ρ' : L → V' →L[K] V') {k : ℕ}
  (P : ContinuousMultilinearMap K (fun _ : Fin k => chainSpace ρ →L[K] chainSpace ρ')
    ((chainSpace ρ' [⋀^Fin k]→L[K] K) →L[K] (chainSpace ρ [⋀^Fin k]→L[K] K)))
  (δ : V' [⋀^Fin k]→L[K] K)

/-- The fibre value `π_i(g)(ξ) = P(g¹_{[i]}, …, gᵏ_{[i]})(δ'_i)(ξ_{1[i]}, …, ξ_{k[i]})`. -/
noncomputable def fibreVal (i : List L) (g : Fin k → V →L[K] V') (ξ : Fin k → V) : K :=
  P (fun r => singleOp ρ ρ' i (g r)) (evalForm ρ' δ i) (fun r => singleVec ρ i (ξ r))

/-- Evaluation of an operator at `δ'_i`, followed by restriction to the fibre `V_{[i]}`. -/
noncomputable def fibreRestrict (i : List L) :
    ((chainSpace ρ' [⋀^Fin k]→L[K] K) →L[K] (chainSpace ρ [⋀^Fin k]→L[K] K)) →ₗ[K]
      (V [⋀^Fin k]→ₗ[K] K) :=
  (ContinuousAlternatingMap.toAlternatingMapLinear (R := K)).comp
    ((ContinuousAlternatingMap.compContinuousLinearMapCLM (singleVec ρ i)).toLinearMap.comp
      (ContinuousLinearMap.apply K (chainSpace ρ [⋀^Fin k]→L[K] K)
        (evalForm ρ' δ i)).toLinearMap)

variable [CompleteSpace K] [FiniteDimensional K V]

/-- The fibre map `π_i : Hom_K(V, V')^k → Alt^k_K(V; K)` (F.8). -/
noncomputable def fibreMap (i : List L) :
    MultilinearMap K (fun _ : Fin k => V →ₗ[K] V') (V [⋀^Fin k]→ₗ[K] K) :=
  (fibreRestrict ρ ρ' δ i).compMultilinearMap
    (P.toMultilinearMap.compLinearMap fun _ =>
      (singleOp ρ ρ' i).toLinearMap.comp
        (LinearMap.toContinuousLinearMap : (V →ₗ[K] V') ≃ₗ[K] (V →L[K] V')).toLinearMap)

theorem fibreMap_apply (i : List L) (g : Fin k → V →ₗ[K] V') (ξ : Fin k → V) :
    fibreMap ρ ρ' P δ i g ξ =
      fibreVal ρ ρ' P δ i (fun r => LinearMap.toContinuousLinearMap (g r)) ξ :=
  rfl

/-- **(F.9).** If `P` lifts the precomposition action, then `π_i(g, …, g) = δ ∘ (g, …, g)`. -/
theorem fibreMap_diag
    (hP : ∀ f, P (fun _ => f) = ContinuousAlternatingMap.compContinuousLinearMapCLM f)
    (i : List L) (g : V →ₗ[K] V') :
    fibreMap ρ ρ' P δ i (fun _ => g) = δ.toAlternatingMap.compLinearMap g := by
  ext ξ
  rw [fibreMap_apply, fibreVal, hP]
  simp only [ContinuousAlternatingMap.compContinuousLinearMapCLM_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, evalForm_apply, Function.comp_apply,
    singleOp_apply,
    coe_singleVec_apply, evalAt_apply, lp.single_apply_self, AlternatingMap.compLinearMap_apply,
    ContinuousAlternatingMap.coe_toAlternatingMap, LinearMap.coe_toContinuousLinearMap']

end AlternatingAnalytic.ChainSpaces
