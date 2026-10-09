import AlternatingAnalytic.Analysis.LaurentField
import AlternatingAnalytic.Analysis.ProjectiveExterior

/-!
# Lemma C.2 (the projective exterior norm), pp. 36-37

Paper statement (Appendix C, `Lemma C.2`; setting §C.1: `k ≥ 1`, `κ` a field, `r ∈ (0, 1)`,
`K₁ = κ((X))` with `|a| = r^{ord a}`, `E₁ = ℓ^∞(ℕ, K₁)`): on `Λ := Λ^k_{K₁} E₁` put
`‖ω‖_π := inf { ∑_j ∏_{i=1}^k ‖x_{j,i}‖_∞ : ω = ∑_j x_{j,1} ∧ ⋯ ∧ x_{j,k} }` (infimum over
finite decompositions, ordinary sum), and let `Ω^{K₁} : Λ → ℓ^∞(ℕ^k, K₁)` be the determinant
array, `Ω^{K₁}(x₁ ∧ ⋯ ∧ x_k)(i₁,…,i_k) = det(x_b(i_a))_{a,b}`. Then `‖·‖_π` is a `K₁`-norm on
`Λ` with `‖x₁ ∧ ⋯ ∧ x_k‖_π ≤ ∏_i ‖x_i‖_∞`, and `Ω^{K₁}` is `K₁`-linear and injective with
`‖Ω^{K₁}(ω)‖_∞ ≤ ‖ω‖_π`. Let `B` be the completion of `(Λ, ‖·‖_π)`, a `K₁`-Banach space,
`J : B → ℓ^∞(ℕ^k, K₁)` the continuous extension of `Ω^{K₁}` (so `‖J‖ ≤ 1`), and
`W_B : E₁^k → B`, `W_B(x) := x₁ ∧ ⋯ ∧ x_k`. Then `W_B ∈ Alt^k_{K₁}(E₁; B)`, `‖W_B‖ ≤ 1`, and
`J(W_B(x)) = Ω^{K₁}(x₁ ∧ ⋯ ∧ x_k)`.

## Formalization notes
* The degree index type is `Fin k`; `k ≥ 1` is the hypothesis `hk`.
* `K₁` is the library's `LaurentField κ r` (`LaurentSeries κ` with the `r`-adic norm,
  `0 < r < 1` as `Fact` instances), `E₁ = ℕ →ᵇ K₁` and `Λ = ⋀[K₁]^k E₁`.
* `projNorm` is `‖·‖_π`, with finite decompositions encoded as lists of `k`-tuples. "`K₁`-norm"
  is spelled out as the triangle inequality, homogeneity and definiteness (part 1).
* Part 2 asserts that some `K₁`-linear `Ω : Λ → ((Fin k → ℕ) → K₁)` satisfies the determinant
  formula on pure wedges (which determines it), is injective, and has every entry bounded by
  `‖ω‖_π`.
* Part 3 takes `B` to be the library's `ProjectiveExteriorCompletion K₁ ℕ k` and states that it
  is the completion of `(Λ, ‖·‖_π)`: `B` is complete and `toB : Λ → B` is linear, isometric and
  has dense range. `J` and `W_B` are asserted to exist with the stated formulas, `J` landing in
  `(Fin k → ℕ) →ᵇ K₁`.
* `set_option backward.isDefEq.respectTransparency false` is needed for instance search on
  `ℕ →ᵇ K₁`; it does not change any statement.
-/

set_option backward.isDefEq.respectTransparency false

open scoped NNReal BoundedContinuousFunction

namespace AlternatingAnalyticChallenge.LemC_2

open AlternatingAnalytic

universe u

/-- The projective exterior norm `‖ω‖_π`: the infimum, over all finite decompositions
`ω = ∑_j x_{j,1} ∧ ⋯ ∧ x_{j,k}` (lists of `k`-tuples), of `∑_j ∏_i ‖x_{j,i}‖`. -/
noncomputable def projNorm (K : Type*) [NormedField K] (V : Type*) [SeminormedAddCommGroup V]
    [NormedSpace K V] (k : ℕ) (ω : ⋀[K]^k V) : ℝ :=
  ⨅ l : {l : List (Fin k → V) // (l.map (exteriorPower.ιMulti K k)).sum = ω},
    (l.1.map fun x => ∏ i, ‖x i‖).sum

/-- The canonical map from `Λ = ⋀[K₁]^k E₁` into the completion `B`. -/
noncomputable def toB (κ : Type u) [Field κ] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] (k : ℕ)
    (ω : ⋀[LaurentField κ r]^k (ℕ →ᵇ LaurentField κ r)) :
    ProjectiveExteriorCompletion (LaurentField κ r) ℕ k :=
  ((show ProjectiveExterior (LaurentField κ r) ℕ k from ω :
    ProjectiveExterior (LaurentField κ r) ℕ k) :
      ProjectiveExteriorCompletion (LaurentField κ r) ℕ k)

/-- `‖·‖_π` is a `K₁`-norm on `Λ`, and `‖x₁ ∧ ⋯ ∧ x_k‖_π ≤ ∏ i, ‖x i‖`. -/
theorem part1_projNorm_isNorm
    (κ : Type u) [Field κ] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] (k : ℕ) (hk : 1 ≤ k) :
    (∀ ω η : ⋀[LaurentField κ r]^k (ℕ →ᵇ LaurentField κ r),
      projNorm (LaurentField κ r) (ℕ →ᵇ LaurentField κ r) k (ω + η) ≤
        projNorm (LaurentField κ r) (ℕ →ᵇ LaurentField κ r) k ω +
          projNorm (LaurentField κ r) (ℕ →ᵇ LaurentField κ r) k η) ∧
    (∀ (a : LaurentField κ r) (ω : ⋀[LaurentField κ r]^k (ℕ →ᵇ LaurentField κ r)),
      projNorm (LaurentField κ r) (ℕ →ᵇ LaurentField κ r) k (a • ω) =
        ‖a‖ * projNorm (LaurentField κ r) (ℕ →ᵇ LaurentField κ r) k ω) ∧
    (∀ ω : ⋀[LaurentField κ r]^k (ℕ →ᵇ LaurentField κ r),
      projNorm (LaurentField κ r) (ℕ →ᵇ LaurentField κ r) k ω = 0 ↔ ω = 0) ∧
    (∀ x : Fin k → (ℕ →ᵇ LaurentField κ r),
      projNorm (LaurentField κ r) (ℕ →ᵇ LaurentField κ r) k
        (exteriorPower.ιMulti (LaurentField κ r) k x) ≤ ∏ i, ‖x i‖) := by
  sorry

/-- The determinant array `Ω^{K₁}` is `K₁`-linear and injective, with
`‖Ω^{K₁}(ω)‖_∞ ≤ ‖ω‖_π`. -/
theorem part2_determinantArray
    (κ : Type u) [Field κ] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] (k : ℕ) (hk : 1 ≤ k) :
    ∃ Ω : (⋀[LaurentField κ r]^k (ℕ →ᵇ LaurentField κ r)) →ₗ[LaurentField κ r]
        ((Fin k → ℕ) → LaurentField κ r),
      (∀ (x : Fin k → (ℕ →ᵇ LaurentField κ r)) (c : Fin k → ℕ),
        Ω (exteriorPower.ιMulti (LaurentField κ r) k x) c =
          Matrix.det (fun a b => x b (c a))) ∧
      Function.Injective Ω ∧
      (∀ (ω : ⋀[LaurentField κ r]^k (ℕ →ᵇ LaurentField κ r)) (c : Fin k → ℕ),
        ‖Ω ω c‖ ≤ projNorm (LaurentField κ r) (ℕ →ᵇ LaurentField κ r) k ω) := by
  sorry

/-- `B` is the completion of `(Λ, ‖·‖_π)`, the extension `J` of `Ω^{K₁}` has norm at most one,
and `W_B(x) = x₁ ∧ ⋯ ∧ x_k` is a continuous alternating map of norm at most one with
`J (W_B x) = Ω^{K₁}(x₁ ∧ ⋯ ∧ x_k)`. -/
theorem part3_completion
    (κ : Type u) [Field κ] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] (k : ℕ) (hk : 1 ≤ k) :
    CompleteSpace (ProjectiveExteriorCompletion (LaurentField κ r) ℕ k) ∧
    (∀ (a : LaurentField κ r) (ω η : ⋀[LaurentField κ r]^k (ℕ →ᵇ LaurentField κ r)),
      toB κ r k (a • ω + η) = a • toB κ r k ω + toB κ r k η) ∧
    (∀ ω : ⋀[LaurentField κ r]^k (ℕ →ᵇ LaurentField κ r),
      ‖toB κ r k ω‖ = projNorm (LaurentField κ r) (ℕ →ᵇ LaurentField κ r) k ω) ∧
    DenseRange (toB κ r k) ∧
    ∃ J : ProjectiveExteriorCompletion (LaurentField κ r) ℕ k →L[LaurentField κ r]
        ((Fin k → ℕ) →ᵇ LaurentField κ r),
      ‖J‖ ≤ 1 ∧
      (∀ (x : Fin k → (ℕ →ᵇ LaurentField κ r)) (c : Fin k → ℕ),
        J (toB κ r k (exteriorPower.ιMulti (LaurentField κ r) k x)) c =
          Matrix.det (fun a b => x b (c a))) ∧
      ∃ W : (ℕ →ᵇ LaurentField κ r) [⋀^Fin k]→L[LaurentField κ r]
          ProjectiveExteriorCompletion (LaurentField κ r) ℕ k,
        (∀ x : Fin k → (ℕ →ᵇ LaurentField κ r),
          W x = toB κ r k (exteriorPower.ιMulti (LaurentField κ r) k x)) ∧
        ‖W‖ ≤ 1 ∧
        (∀ (x : Fin k → (ℕ →ᵇ LaurentField κ r)) (c : Fin k → ℕ),
          J (W x) c = Matrix.det (fun a b => x b (c a))) := by
  sorry

end AlternatingAnalyticChallenge.LemC_2
