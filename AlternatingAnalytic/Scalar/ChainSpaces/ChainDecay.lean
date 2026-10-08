import AlternatingAnalytic.Scalar.ChainSpaces.ChainForm
import AlternatingAnalytic.Scalar.ChainSpaces.FibreMap
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

/-!
# Chain decay of the fibre values

Fix a label `j`, a `j`-chain sequence `s`, maps `g¹, …, gᵏ : V → V'` sending `ker (ρ j)` into
`ker (ρ' j)` and vectors `ξ₁, …, ξ_k ∈ ker (ρ j)`. From a bounded `k`-linear `P` we build the
bounded `(2k+1)`-linear scalar form on `ℓ^∞(List L, K)`
`Φ(t¹, …, tᵏ, c, r¹, …, rᵏ) = P(u_{t¹}, …, u_{tᵏ})(m_c)(r¹x¹, …, rᵏxᵏ)` (`chainTestForm`),
where `u_t = chainOp`, `m_c = chainForm`, `r ↦ r x = chainVec`. At the coordinate vector of a
chain word `s n` its diagonal value is the fibre value `π_{s n}(g)(ξ)` (`chainTestForm_single`).
Hence the multilinear tail property (Lemma F.2, entering as the hypothesis `hdiag`: diagonal
values of bounded multilinear forms on `ℓ^∞` tend to zero) gives
`π_{s n}(g)(ξ) → 0` along the chain (F.10, `tendsto_fibreVal`).
-/

open Filter Topology
open scoped ENNReal

set_option maxSynthPendingDepth 2

namespace AlternatingAnalytic.ChainSpaces

variable {K : Type*} [NontriviallyNormedField K] {L : Type*} [DecidableEq L]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace K V]
  {V' : Type*} [NormedAddCommGroup V'] [NormedSpace K V']
  (ρ : L → V →L[K] V) (ρ' : L → V' →L[K] V')

section Single

variable {j : L} {s : ℕ → List L} (hs : IsChainSeq j s)

theorem chainOp_single (hidem : ∀ v, ρ j (ρ j v) = ρ j v) (hidem' : ∀ v, ρ' j (ρ' j v) = ρ' j v)
    {g : V →L[K] V'} (hg : ∀ v, ρ j v = 0 → ρ' j (g v) = 0) (n : ℕ) :
    chainOp ρ ρ' hs hidem hidem' hg (lp.single ∞ (s n) 1) = singleOp ρ ρ' (s n) g := by
  refine ContinuousLinearMap.ext fun x => Subtype.ext <| lp.ext <| funext fun w => ?_
  rw [coe_chainOp_apply, singleOp_apply, coe_singleVec_apply, evalAt_apply]
  by_cases hw : w = s n
  · subst hw
    rw [Set.indicator_of_mem (Set.mem_range_self n)]
    simp
  · have h0 : (lp.single ∞ (s n) (1 : K) : List L → K) w = 0 :=
      lp.single_apply_ne (E := fun _ => K) ∞ (s n) 1 hw
    have h1 : (lp.single ∞ (s n) (g ((x : lp (fun _ : List L => V) ∞) (s n))) :
        List L → V') w = 0 := lp.single_apply_ne (E := fun _ => V') ∞ (s n) _ hw
    rw [h1]
    by_cases hw' : w ∈ Set.range s
    · rw [Set.indicator_of_mem hw', h0, zero_smul]
    · rw [Set.indicator_of_notMem hw']

theorem chainVec_single {v : V} (hv : ρ j v = 0) (n : ℕ) :
    chainVec ρ hs hv (lp.single ∞ (s n) 1) = singleVec ρ (s n) v := by
  refine Subtype.ext <| lp.ext <| funext fun w => ?_
  rw [coe_chainVec_apply, coe_singleVec_apply]
  by_cases hw : w = s n
  · subst hw
    rw [Set.indicator_of_mem (Set.mem_range_self n)]
    simp
  · have h0 : (lp.single ∞ (s n) (1 : K) : List L → K) w = 0 :=
      lp.single_apply_ne (E := fun _ => K) ∞ (s n) 1 hw
    have h1 : (lp.single ∞ (s n) v : List L → V) w = 0 :=
      lp.single_apply_ne (E := fun _ => V) ∞ (s n) _ hw
    rw [h1]
    by_cases hw' : w ∈ Set.range s
    · rw [Set.indicator_of_mem hw', h0, zero_smul]
    · rw [Set.indicator_of_notMem hw']

end Single

variable [CompleteSpace K] [IsUltrametricDist K] {k : ℕ}
  (P : ContinuousMultilinearMap K (fun _ : Fin k => chainSpace ρ →L[K] chainSpace ρ')
    ((chainSpace ρ' [⋀^Fin k]→L[K] K) →L[K] (chainSpace ρ [⋀^Fin k]→L[K] K)))
  (δ : V' [⋀^Fin k]→L[K] K)
  {j : L} {s : ℕ → List L} (hs : IsChainSeq j s) (hidem : ∀ v, ρ j (ρ j v) = ρ j v)
  (hidem' : ∀ v, ρ' j (ρ' j v) = ρ' j v) (hδ : ∀ z : Fin k → V', (∀ r, ρ' j (z r) = 0) → δ z = 0)
  {g : Fin k → V →L[K] V'} (hg : ∀ r v, ρ j v = 0 → ρ' j (g r v) = 0)
  {ξ : Fin k → V} (hξ : ∀ r, ρ j (ξ r) = 0)

/-- `β ↦ (r ↦ β(r¹x¹, …, rᵏxᵏ))`, from `Alt(E; K)` to `k`-linear forms on `ℓ^∞(List L, K)`. -/
noncomputable def chainTestN :
    (chainSpace ρ [⋀^Fin k]→L[K] K) →L[K]
      ContinuousMultilinearMap K (fun _ : Fin k => lp (fun _ : List L => K) ∞) K :=
  (ContinuousMultilinearMap.compContinuousLinearMapL (fun r => chainVec ρ hs (hξ r))).comp
    (ContinuousAlternatingMap.toContinuousMultilinearMapCLM K)

/-- `O ↦ (c ↦ (r ↦ O(m_c)(r¹x¹, …, rᵏxᵏ)))`. -/
noncomputable def chainTestW :
    ((chainSpace ρ' [⋀^Fin k]→L[K] K) →L[K] (chainSpace ρ [⋀^Fin k]→L[K] K)) →L[K]
      (lp (fun _ : List L => K) ∞ →L[K]
        ContinuousMultilinearMap K (fun _ : Fin k => lp (fun _ : List L => K) ∞) K) :=
  (ContinuousLinearMap.compL K (lp (fun _ : List L => K) ∞) (chainSpace ρ [⋀^Fin k]→L[K] K)
      (ContinuousMultilinearMap K (fun _ : Fin k => lp (fun _ : List L => K) ∞) K)
      (chainTestN ρ hs hξ)).comp
    ((ContinuousLinearMap.compL K (lp (fun _ : List L => K) ∞) (chainSpace ρ' [⋀^Fin k]→L[K] K)
      (chainSpace ρ [⋀^Fin k]→L[K] K)).flip (chainForm ρ' hs hidem' δ hδ))

/-- `t ↦ (c ↦ (r ↦ Φ(t, c, r)))`. -/
noncomputable def chainTestCurried :
    ContinuousMultilinearMap K (fun _ : Fin k => lp (fun _ : List L => K) ∞)
      (lp (fun _ : List L => K) ∞ →L[K]
        ContinuousMultilinearMap K (fun _ : Fin k => lp (fun _ : List L => K) ∞) K) :=
  (chainTestW ρ ρ' δ hs hidem' hδ hξ).compContinuousMultilinearMap
    (P.compContinuousLinearMap fun r => chainOp ρ ρ' hs hidem hidem' (hg r))

/-- `F ↦ F.uncurryLeft`, as a continuous linear map. -/
noncomputable def uncurryLeftCLM (k : ℕ) :
    (lp (fun _ : List L => K) ∞ →L[K]
        ContinuousMultilinearMap K (fun _ : Fin k => lp (fun _ : List L => K) ∞) K) →L[K]
      ContinuousMultilinearMap K (fun _ : Fin (k + 1) => lp (fun _ : List L => K) ∞) K :=
  ((continuousMultilinearCurryLeftEquiv K
    (fun _ : Fin (k + 1) => lp (fun _ : List L => K) ∞) K).symm.toLinearIsometry).toContinuousLinearMap

/-- The `(k + (k + 1))`-linear form `Φ(t, c, r) = P(u_{t¹}, …, u_{tᵏ})(m_c)(r¹x¹, …, rᵏxᵏ)` on
`ℓ^∞(List L, K)`. -/
noncomputable def chainTestForm :
    ContinuousMultilinearMap K (fun _ : Fin (k + (k + 1)) => lp (fun _ : List L => K) ∞) K :=
  (((uncurryLeftCLM (K := K) (L := L) k).compContinuousMultilinearMap
    (chainTestCurried ρ ρ' P δ hs hidem hidem' hδ hg hξ)).uncurrySum).domDomCongr finSumFinEquiv

omit [DecidableEq L] in
theorem chainTestForm_diag (e : lp (fun _ : List L => K) ∞) :
    chainTestForm ρ ρ' P δ hs hidem hidem' hδ hg hξ (fun _ => e) =
      P (fun r => chainOp ρ ρ' hs hidem hidem' (hg r) e) (chainForm ρ' hs hidem' δ hδ e)
        (fun r => chainVec ρ hs (hξ r) e) :=
  rfl

/-- At the coordinate vector of a chain word `s n`, the diagonal value of `Φ` is the fibre value
`π_{s n}(g)(ξ)`. -/
theorem chainTestForm_single (n : ℕ) :
    chainTestForm ρ ρ' P δ hs hidem hidem' hδ hg hξ (fun _ => lp.single ∞ (s n) 1) =
      fibreVal ρ ρ' P δ (s n) g ξ := by
  rw [chainTestForm_diag, fibreVal, chainForm_single]
  simp only [chainOp_single, chainVec_single]

/-- **(F.10) Chain decay.** Given the multilinear tail property of `ℓ^∞(List L, K)` in degree
`k + (k + 1)`, the fibre values `π_{s n}(g)(ξ)` tend to zero along the chain. -/
theorem tendsto_fibreVal (hs : IsChainSeq j s) (hidem : ∀ v, ρ j (ρ j v) = ρ j v)
    (hidem' : ∀ v, ρ' j (ρ' j v) = ρ' j v)
    (hδ : ∀ z : Fin k → V', (∀ r, ρ' j (z r) = 0) → δ z = 0)
    (hg : ∀ r v, ρ j v = 0 → ρ' j (g r v) = 0) (hξ : ∀ r, ρ j (ξ r) = 0)
    (hdiag : ∀ μ : ContinuousMultilinearMap K
        (fun _ : Fin (k + (k + 1)) => lp (fun _ : List L => K) ∞) K,
      Tendsto (fun i => μ (fun _ => lp.single ∞ i 1)) cofinite (𝓝 0)) :
    Tendsto (fun n => fibreVal ρ ρ' P δ (s n) g ξ) atTop (𝓝 0) := by
  have h := (hdiag (chainTestForm ρ ρ' P δ hs hidem hidem' hδ hg hξ)).comp
    hs.injective.tendsto_cofinite
  rw [Nat.cofinite_eq_atTop] at h
  simpa only [Function.comp_def, chainTestForm_single] using h

end AlternatingAnalytic.ChainSpaces
