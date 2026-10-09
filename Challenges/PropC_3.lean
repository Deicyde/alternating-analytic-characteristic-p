import AlternatingAnalytic.Analysis.LaurentField
import AlternatingAnalytic.Analysis.ProjectiveExterior
import AlternatingAnalytic.Algebra.ExteriorSupportDimension

/-!
# Proposition C.3 (support estimate), pp. 37-38

Paper statement (Appendix C, `Proposition C.3`; setting §C.1: `k ≥ 1`, `κ` a field,
`r ∈ (0, 1)`, `K₁ = κ((X))`, `E₁ = ℓ^∞(ℕ, K₁)`, `E₀ = κ^ℕ ⊆ E₁`, `B`, `J` as in Lemma C.2,
`coeff₀` the coordinatewise constant Laurent coefficient, `M_r := max_{l ∈ ℕ} (l + 1) r^l`,
`Ω^κ : Λ^k_κ E₀ → κ^{ℕ^k}` the determinant array over `κ`): For every `b ∈ B` there is a unique
`η(b) ∈ Λ^k_κ E₀` with `Ω^κ(η(b)) = coeff₀(J b)`. The map `η` is `κ`-linear, and
`sdim(η(b)) ≤ k M_r ‖b‖_B` for all `b ∈ B` (C.2).

## Formalization notes
* Degree: the index type is `Fin k`; `k ≥ 1` is `hk : 1 ≤ k`. `κ` is an arbitrary field
  (Remark C.5: Proposition C.3 holds for every field `κ`).
* `K₁ = AlternatingAnalytic.LaurentField κ r`, `E₁ = ℕ →ᵇ K₁`, `E₀ = ℕ → κ`,
  `Λ^k_κ E₀ = ⋀[κ]^k (ℕ → κ)`.
* `B` and `J` are the library's `ProjectiveExteriorCompletion K₁ ℕ k` and
  `completedExteriorArray K₁ ℕ k : B →L[K₁] ((Fin k → ℕ) →ᵇ K₁)` (the continuous extension of the
  determinant array; that these are the completion of `(Λ, ‖·‖_π)` and the extension of
  `Ω^{K₁}` is the content of challenge `LemC_2`), imported from `ProjectiveExterior.lean` for these
  definitions only.
* `Ω^κ` is not imported: the theorem quantifies over every `κ`-linear
  `Ωκ : ⋀[κ]^k (ℕ → κ) → ((Fin k → ℕ) → κ)` with `Ωκ(y₁ ∧ ⋯ ∧ y_k)(c) = det(y_b(c_a))_{a,b}`;
  this formula determines `Ωκ` uniquely.
* `coeff₀` (introduced here as `coeff0`) uses the library's coefficient map
  `LaurentField.coeff κ r 0` (Mathlib's `HahnSeries.coeff · 0`).
* `M_r` (introduced here as `Mr`) is `⨆ l : ℕ, (l + 1) r^l`; the supremum is attained (a maximum).
* `sdim` is the library's `AlternatingAnalytic.exteriorSupportDim` (least `finrank` of a
  finite-dimensional subspace `W ⊆ E₀` with `ω ∈ Λ^k W`, `Algebra/ExteriorSupportDimension.lean`),
  imported for this definition.
* `κ`-linearity of `η` is stated as additivity and `η(c • b) = c • η(b)` for `c ∈ κ` acting
  through `algebraMap κ K₁`.
* Universe: `κ : Type u`.
* `set_option backward.isDefEq.respectTransparency false` (as in the library) is needed for
  instance search on `ℕ →ᵇ K₁`; it does not change any statement.
-/

set_option backward.isDefEq.respectTransparency false

open scoped NNReal BoundedContinuousFunction

namespace AlternatingAnalyticChallenge.PropC_3

open AlternatingAnalytic

universe u

/-- The constant-coefficient map `coeff₀ : ℓ^∞(S, κ((X))) → κ^S`, taken coordinatewise. -/
noncomputable def coeff0 (κ : Type u) [Field κ] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] {S : Type*}
    [TopologicalSpace S] (y : S →ᵇ LaurentField κ r) : S → κ :=
  fun s => LaurentField.coeff κ r 0 (y s)

/-- `M_r := max_{l ∈ ℕ} (l + 1) r^l`. -/
noncomputable def Mr (r : ℝ≥0) : ℝ := ⨆ l : ℕ, ((l : ℝ) + 1) * (r : ℝ) ^ l

/-- **Proposition C.3 (support estimate).** -/
theorem support_estimate
    (κ : Type u) [Field κ] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] (k : ℕ) (hk : 1 ≤ k)
    (Ωκ : (⋀[κ]^k (ℕ → κ)) →ₗ[κ] ((Fin k → ℕ) → κ))
    (hΩκ : ∀ (y : Fin k → ℕ → κ) (c : Fin k → ℕ),
      Ωκ (exteriorPower.ιMulti κ k y) c = Matrix.det (fun a b => y b (c a))) :
    ∃ η : ProjectiveExteriorCompletion (LaurentField κ r) ℕ k → ⋀[κ]^k (ℕ → κ),
      (∀ b : ProjectiveExteriorCompletion (LaurentField κ r) ℕ k,
        Ωκ (η b) = coeff0 κ r (completedExteriorArray (LaurentField κ r) ℕ k b)) ∧
      (∀ (b : ProjectiveExteriorCompletion (LaurentField κ r) ℕ k) (β : ⋀[κ]^k (ℕ → κ)),
        Ωκ β = coeff0 κ r (completedExteriorArray (LaurentField κ r) ℕ k b) → β = η b) ∧
      (∀ b b' : ProjectiveExteriorCompletion (LaurentField κ r) ℕ k,
        η (b + b') = η b + η b') ∧
      (∀ (c : κ) (b : ProjectiveExteriorCompletion (LaurentField κ r) ℕ k),
        η (algebraMap κ (LaurentField κ r) c • b) = c • η b) ∧
      (∀ b : ProjectiveExteriorCompletion (LaurentField κ r) ℕ k,
        (exteriorSupportDim (η b) : ℝ) ≤ (k : ℝ) * Mr r * ‖b‖) := by
  sorry

end AlternatingAnalyticChallenge.PropC_3
