import AlternatingAnalytic.Scalar.ChainSpaces.ChainDecay
import AlternatingAnalytic.Analysis.LiftCriterion

/-!
# No bounded lift between chain-limit spaces

The proof of Theorem F.1, for an abstract finite label set `L`. Let `ρ`, `ρ'` be idempotent
residual maps on finite-dimensional `V`, `V'`, `δ` a
continuous alternating `k`-form on `V'` vanishing on every `(ker ρ' j)^k`, and `g₀ : V → V'`.
Suppose finite test sets certify that every `k`-linear `τ` with `τ(g₀, …, g₀) = δ ∘ (g₀, …, g₀)`
has a test of absolute value at least `1` (`TestCertificate`, the conclusion of Lemma F.5), and
that diagonal values of bounded multilinear forms on `ℓ^∞(List L, K)` tend to zero (Lemma F.2).
Then precomposition `A^k : L(E, E') → L(Alt^k(E'; K), Alt^k(E; K))` between the chain-limit
spaces has no bounded `k`-linear lift (`no_bounded_lift`): the fibre maps `π_i` satisfy (F.9)
and decay along chains (F.10), so the sets `a_j = {i : all tests of j are < 1 at π_i}` contain
cofinitely many words of every `j`-chain, and the chain gap lemma (Lemma F.3) gives a word in all
`a_j`, contradicting the certificate. By the lift criterion (Proposition 3.3), `A^k` is then
analytic at no point (`not_analyticAt_compContinuousLinearMapCLM`).
-/

open Filter Topology
open scoped ENNReal

set_option maxSynthPendingDepth 2

namespace AlternatingAnalytic.ChainSpaces

variable {K : Type*} [NontriviallyNormedField K] {L : Type*}
  {V : Type*} [NormedAddCommGroup V] [NormedSpace K V]
  {V' : Type*} [NormedAddCommGroup V'] [NormedSpace K V']

/-- Finite test certificate (the conclusion of Lemma F.5, for the label family `ρ`, `ρ'`):
finite sets of tests `(g; ξ)` for each label `j`, with every `g^r` mapping `ker (ρ j)` into
`ker (ρ' j)` and every `ξ_r ∈ ker (ρ j)`, such that every `k`-linear `τ` with
`τ(g₀, …, g₀) = δ ∘ (g₀, …, g₀)` has a test value of absolute value at least `1`. -/
def TestCertificate {k : ℕ} (ρ : L → V →L[K] V) (ρ' : L → V' →L[K] V') (g₀ : V →ₗ[K] V')
    (δ : V' [⋀^Fin k]→ₗ[K] K) : Prop :=
  ∃ T : L → Finset ((Fin k → (V →ₗ[K] V')) × (Fin k → V)),
    (∀ j, ∀ t ∈ T j, (∀ r v, ρ j v = 0 → ρ' j (t.1 r v) = 0) ∧ ∀ r, ρ j (t.2 r) = 0) ∧
    ∀ τ : MultilinearMap K (fun _ : Fin k => V →ₗ[K] V') (V [⋀^Fin k]→ₗ[K] K),
      τ (fun _ => g₀) = δ.compLinearMap g₀ → ∃ j, ∃ t ∈ T j, 1 ≤ ‖τ t.1 t.2‖

variable [CompleteSpace K] [IsUltrametricDist K] [Fintype L] [DecidableEq L]
  [FiniteDimensional K V] (ρ : L → V →L[K] V) (ρ' : L → V' →L[K] V') {k : ℕ}

/-- Under the test certificate and the multilinear tail property, the
precomposition action between the chain-limit spaces has no bounded `k`-linear lift. -/
theorem no_bounded_lift (hidem : ∀ j v, ρ j (ρ j v) = ρ j v)
    (hidem' : ∀ j v, ρ' j (ρ' j v) = ρ' j v) (δ : V' [⋀^Fin k]→L[K] K)
    (hδ : ∀ j (z : Fin k → V'), (∀ r, ρ' j (z r) = 0) → δ z = 0) (g₀ : V →ₗ[K] V')
    (hcert : TestCertificate ρ ρ' g₀ δ.toAlternatingMap)
    (hdiag : ∀ μ : ContinuousMultilinearMap K
        (fun _ : Fin (k + (k + 1)) => lp (fun _ : List L => K) ∞) K,
      Tendsto (fun i => μ (fun _ => lp.single ∞ i 1)) cofinite (𝓝 0))
    (P : ContinuousMultilinearMap K (fun _ : Fin k => chainSpace ρ →L[K] chainSpace ρ')
      ((chainSpace ρ' [⋀^Fin k]→L[K] K) →L[K] (chainSpace ρ [⋀^Fin k]→L[K] K)))
    (hP : ∀ f, P (fun _ => f) = ContinuousAlternatingMap.compContinuousLinearMapCLM f) :
    False := by
  obtain ⟨T, hT, hcert⟩ := hcert
  let a : L → Set (List L) := fun j => {i | ∀ t ∈ T j, ‖fibreMap ρ ρ' P δ i t.1 t.2‖ < 1}
  have ha : ∀ j T', ChainGap.IsLabelChain j T' → (T' \ a j).Finite := by
    rintro j _ ⟨s, hs, rfl⟩
    have hev : ∀ t ∈ T j, ∀ᶠ n in atTop, ‖fibreMap ρ ρ' P δ (s n) t.1 t.2‖ < 1 := by
      intro t ht
      have h := tendsto_fibreVal ρ ρ' P δ (g := fun r => LinearMap.toContinuousLinearMap (t.1 r))
        (ξ := t.2) hs (hidem j) (hidem' j) (hδ j) (fun r v hv => (hT j t ht).1 r v hv)
        (fun r => (hT j t ht).2 r) hdiag
      have h1 := h.norm
      rw [norm_zero] at h1
      exact h1.eventually (gt_mem_nhds zero_lt_one)
    have hall : ∀ᶠ n in atTop, s n ∈ a j := (eventually_all_finset (T j)).2 hev
    rw [← Nat.cofinite_eq_atTop, eventually_cofinite] at hall
    refine (hall.image s).subset ?_
    rintro _ ⟨⟨n, rfl⟩, hn⟩
    exact ⟨n, hn, rfl⟩
  obtain ⟨i, hi⟩ := ChainGap.iInter_nonempty_of_cofinite_on_chains a ha
  obtain ⟨j, t, ht, hge⟩ := hcert (fibreMap ρ ρ' P δ i) (fibreMap_diag ρ ρ' P δ hP i g₀)
  exact absurd hge (not_le.2 (Set.mem_iInter.1 hi j t ht))

/-- Under the same hypotheses, the precomposition action between the
chain-limit spaces is analytic at no point (Proposition 3.3). -/
theorem not_analyticAt_compContinuousLinearMapCLM (hidem : ∀ j v, ρ j (ρ j v) = ρ j v)
    (hidem' : ∀ j v, ρ' j (ρ' j v) = ρ' j v) (δ : V' [⋀^Fin k]→L[K] K)
    (hδ : ∀ j (z : Fin k → V'), (∀ r, ρ' j (z r) = 0) → δ z = 0) (g₀ : V →ₗ[K] V')
    (hcert : TestCertificate ρ ρ' g₀ δ.toAlternatingMap)
    (hdiag : ∀ μ : ContinuousMultilinearMap K
        (fun _ : Fin (k + (k + 1)) => lp (fun _ : List L => K) ∞) K,
      Tendsto (fun i => μ (fun _ => lp.single ∞ i 1)) cofinite (𝓝 0))
    (u₀ : chainSpace ρ →L[K] chainSpace ρ') :
    ¬ AnalyticAt K
      (fun u : chainSpace ρ →L[K] chainSpace ρ' =>
        (ContinuousAlternatingMap.compContinuousLinearMapCLM u :
          (chainSpace ρ' [⋀^Fin k]→L[K] K) →L[K] (chainSpace ρ [⋀^Fin k]→L[K] K))) u₀ := by
  intro h
  obtain ⟨P, hP⟩ := LiftCriterion.hasBoundedLift_iff_exists_ι.1
    (LiftCriterion.hasBoundedLift_of_analyticAt (𝕜 := K) (ι := Fin k) (E := chainSpace ρ)
      (E' := chainSpace ρ') (F := K) h)
  exact no_bounded_lift ρ ρ' hidem hidem' δ hδ g₀ hcert hdiag P hP

end AlternatingAnalytic.ChainSpaces
