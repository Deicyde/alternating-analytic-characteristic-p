import AlternatingAnalytic.Analysis.LaurentField
import AlternatingAnalytic.Analysis.LaurentCoefficients
import AlternatingAnalytic.Analysis.ProjectiveExterior
import AlternatingAnalytic.Algebra.ExteriorSupportDimension

/-!
# Lemma C.4 (the coefficient lift `Ψ`), pp. 37-38

Paper statement (Appendix C, §C.4, `Lemma C.4`; setting §C.1: `k ≥ 1`, `κ` a field,
`r ∈ (0, 1)`, `K₁ = κ((X))`, `E₁ = ℓ^∞(ℕ, K₁)`, `E₀ = κ^ℕ ⊆ E₁`; `B`, `J`, `W_B` as in
Lemma C.2; `η` as in Proposition C.3; `M_r := max_l (l + 1) r^l`): Suppose that `P` is a bounded
`k`-linear lift of `A^{k,K₁}_{E₁,E₁;B}` over `K₁`. For `a ∈ E₁` let `D_a ∈ L(E₁, E₁)` be
coordinatewise multiplication. Define `Φ(a₁,…,a_k; x₁,…,x_k) := P(D_{a₁},…,D_{a_k})(W_B)(x₁,…,x_k)`
and `Ψ := η ∘ Φ|_{E₀^{2k}} : E₀^k × E₀^k → Λ^k_κ E₀`. Then
(Ψ1) `Ψ` is `2k`-linear over `κ`;
(Ψ2) `Ψ` is alternating in the last `k` slots;
(Ψ3) `sdim(Ψ(z)) ≤ d := ⌊k M_r ‖P‖⌋` for all `z ∈ E₀^{2k}`;
(Ψ4) `Ψ` satisfies (Pol) for the multiplier family `D^κ_a x = a x` on `E₀`: for all `m ≥ 1`,
`b₁,…,b_m ∈ E₀`, `α ∈ ℕ^m` with `|α| = k`, and `x ∈ E₀^k`,
`∑_{type f = α} Ψ(b_f; x) = ∑_{type f = α} (b_{f(1)} x₁) ∧ ⋯ ∧ (b_{f(k)} x_k)` in `Λ^k_κ E₀`.
In particular `Ψ` satisfies (Pol1).
Here `f` ranges over maps `[k] → [m]`, `b_f = (b_{f(1)},…,b_{f(k)})`, `type f = (|f⁻¹(j)|)_j`, and
(Pol1) is `∑_{σ ∈ S_k} Ψ(b_{σ(1)},…,b_{σ(k)}; x) = ∑_{σ ∈ S_k} (b_{σ(1)} x₁) ∧ ⋯ ∧ (b_{σ(k)} x_k)`.

## Formalization notes
* Degree: index type `Fin k`; `k ≥ 1` is `hk : 1 ≤ k`. `κ` is an arbitrary field
  (Remark C.5: Lemma C.4 holds for every field `κ`).
* `K₁ = AlternatingAnalytic.LaurentField κ r`, `E₁ = ℕ →ᵇ K₁`, `E₀ = ℕ → κ`, and the inclusion
  `E₀ ⊆ E₁` is the library's `constantLaurentArray κ r` (coordinatewise `algebraMap κ K₁`),
  imported from `LaurentCoefficients.lean` for this definition.
* The bounded `k`-linear lift is `P : ContinuousMultilinearMap K₁ (fun _ : Fin k => E₁ →L[K₁] E₁)
  ((E₁ [⋀^Fin k]→L[K₁] B) →L[K₁] (E₁ [⋀^Fin k]→L[K₁] B))` with
  `P (f, …, f) = compContinuousLinearMapCLM f`.
* `D_a = ContinuousLinearMap.mul K₁ (ℕ →ᵇ K₁) a`. `B`, `J`, `W_B` are the library's
  `ProjectiveExteriorCompletion K₁ ℕ k`, `completedExteriorArray K₁ ℕ k`,
  `completedExteriorWedge K₁ ℕ k` (see challenge `LemC_2`).
* `η` is not imported: the lemma is stated for every map `η : B → Λ^k_κ E₀` with
  `Ω^κ(η b) = coeff₀(J b)` for all `b`, where `Ω^κ` is any `κ`-linear map with the determinant
  formula on pure wedges. By injectivity of `Ω^κ` (Lemma B.2) this pins `η` down to the map of
  Proposition C.3.
* (Ψ1) is the existence of a `κ`-multilinear map in the first `k` slots with values in
  `κ`-multilinear maps of the last `k` slots that agrees with `η ∘ Φ` on `E₀^{2k}`.
* `M_r` is `⨆ l : ℕ, (l + 1) r^l`, `sdim` is the library's `exteriorSupportDim`, `⌊·⌋` is
  `Nat.floor`, and `‖P‖` is the multilinear operator norm
  of `LiftCandidate` (introduced here; the type of `P`), written `liftNorm P` (introduced here).
  Both are defined for general `K, E, F` because elaborating them directly at the concrete Laurent
  spaces times out (the library uses the same device, `BoundedPrecompositionLiftCandidate`).
* `type f` is `selectionType f` (introduced here). In (Ψ4) the label set is `Fin m`.
  (Pol1) is the final conjunct of `coefficient_lift`. (Ψ1)-(Ψ4) and (Pol1) are bundled into the
  single theorem `coefficient_lift` because `Ψ` is existentially quantified and the parts share it.
* Universe: `κ : Type u`.
* `set_option backward.isDefEq.respectTransparency false` (as in the library) is needed for
  instance search on `ℕ →ᵇ K₁`; it does not change any statement.
-/

set_option backward.isDefEq.respectTransparency false

open scoped NNReal BoundedContinuousFunction

namespace AlternatingAnalyticChallenge.LemC_4

open AlternatingAnalytic

universe u

/-- The constant-coefficient map `coeff₀ : ℓ^∞(S, κ((X))) → κ^S`, taken coordinatewise. -/
noncomputable def coeff0 (κ : Type u) [Field κ] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)]
    {S : Type*} [TopologicalSpace S] (y : S →ᵇ LaurentField κ r) : S → κ :=
  fun s => LaurentField.coeff κ r 0 (y s)

/-- `M_r := max_{l ∈ ℕ} (l + 1) r^l`. -/
noncomputable def Mr (r : ℝ≥0) : ℝ := ⨆ l : ℕ, ((l : ℝ) + 1) * (r : ℝ) ^ l

/-- The type of a map `f : [k] → J`: the multiplicity `|f⁻¹(j)|` of each label `j`. -/
noncomputable def selectionType {J : Type*} [Fintype J] {k : ℕ} (f : Fin k → J) (j : J) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => f i = j)).card

/-- Candidates for a bounded `k`-linear lift of `A^k_{E,E;F}`: continuous `k`-linear maps
`L(E,E)^k → L(Alt^k(E;F), Alt^k(E;F))`. -/
abbrev LiftCandidate (K : Type*) [NontriviallyNormedField K]
    (E F : Type*) [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup F] [NormedSpace K F] (k : ℕ) : Type _ :=
  ContinuousMultilinearMap K (fun _ : Fin k => E →L[K] E)
    ((E [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F))

/-- The multilinear operator norm `‖P‖` of a lift candidate. -/
noncomputable def liftNorm {K : Type*} [NontriviallyNormedField K]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup F] [NormedSpace K F] {k : ℕ} (P : LiftCandidate K E F k) : ℝ :=
  @Norm.norm _ (ContinuousMultilinearMap.hasOpNorm (𝕜 := K) (E := fun _ : Fin k => E →L[K] E)
    (G := (E [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F))) P

/-- The hypotheses of Lemma C.4, and its four conclusions. -/
theorem coefficient_lift
    (κ : Type u) [Field κ] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] (k : ℕ) (hk : 1 ≤ k)
    (P : LiftCandidate (LaurentField κ r) (ℕ →ᵇ LaurentField κ r)
      (ProjectiveExteriorCompletion (LaurentField κ r) ℕ k) k)
    (hP : ∀ f : (ℕ →ᵇ LaurentField κ r) →L[LaurentField κ r] (ℕ →ᵇ LaurentField κ r),
      P (fun _ => f) = ContinuousAlternatingMap.compContinuousLinearMapCLM f)
    (Ωκ : (⋀[κ]^k (ℕ → κ)) →ₗ[κ] ((Fin k → ℕ) → κ))
    (hΩκ : ∀ (y : Fin k → ℕ → κ) (c : Fin k → ℕ),
      Ωκ (exteriorPower.ιMulti κ k y) c = Matrix.det (fun a b => y b (c a)))
    (η : ProjectiveExteriorCompletion (LaurentField κ r) ℕ k → ⋀[κ]^k (ℕ → κ))
    (hη : ∀ b : ProjectiveExteriorCompletion (LaurentField κ r) ℕ k,
      Ωκ (η b) = coeff0 κ r (completedExteriorArray (LaurentField κ r) ℕ k b)) :
    ∃ Ψ : MultilinearMap κ (fun _ : Fin k => ℕ → κ)
        (MultilinearMap κ (fun _ : Fin k => ℕ → κ) (⋀[κ]^k (ℕ → κ))),
      -- (Ψ1): `Ψ = η ∘ Φ` on `E₀^{2k}`, and `Ψ` is `2k`-linear over `κ` (by its type)
      (∀ u x : Fin k → ℕ → κ,
        Ψ u x = η (P (fun i => ContinuousLinearMap.mul (LaurentField κ r)
            (ℕ →ᵇ LaurentField κ r) (constantLaurentArray κ r (u i)))
          (completedExteriorWedge (LaurentField κ r) ℕ k)
          (fun i => constantLaurentArray κ r (x i)))) ∧
      -- (Ψ2): alternating in the last `k` slots
      (∀ (u x : Fin k → ℕ → κ) (i j : Fin k), i ≠ j → x i = x j → Ψ u x = 0) ∧
      -- (Ψ3): uniform support bound
      (∀ u x : Fin k → ℕ → κ,
        exteriorSupportDim (Ψ u x) ≤ ⌊(k : ℝ) * Mr r * liftNorm P⌋₊) ∧
      -- (Ψ4): the polarized identity (Pol)
      (∀ (m : ℕ), 1 ≤ m → ∀ (b : Fin m → ℕ → κ) (α : Fin m → ℕ), ∑ j, α j = k →
        ∀ x : Fin k → ℕ → κ,
          (∑ f ∈ Finset.univ.filter (fun f : Fin k → Fin m => selectionType f = α),
              Ψ (fun i => b (f i)) x) =
            ∑ f ∈ Finset.univ.filter (fun f : Fin k → Fin m => selectionType f = α),
              exteriorPower.ιMulti κ k (fun i => b (f i) * x i)) ∧
      -- (Pol1)
      (∀ u x : Fin k → ℕ → κ,
        (∑ σ : Equiv.Perm (Fin k), Ψ (u ∘ σ) x) =
          ∑ σ : Equiv.Perm (Fin k), exteriorPower.ιMulti κ k (fun i => u (σ i) * x i)) := by
  sorry

end AlternatingAnalyticChallenge.LemC_4
