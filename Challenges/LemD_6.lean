import AlternatingAnalytic.Analysis.SphericalCompleteness
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Algebra.Algebra.Bilinear

/-!
# Lemma D.6 (projective base change), p. 43

Setting (§D.2–D.3): fields K₁ ⊆ K′ with "(H1) K₁, with the restricted absolute value, is
nontrivially normed, complete and spherically complete. (H2) K′ is nonarchimedean." For a
normed K₁-space V, V_{K′} := V ⊗_{K₁} K′ (a K′-vector space through the second factor) with
‖u‖_π := inf{∑ⱼ ‖xⱼ‖ |λⱼ| : u = ∑ⱼ xⱼ ⊗ λⱼ}, the infimum over finite decompositions, with an
ordinary sum. For bounded K₁-linear ψ : K′ → K₁, T_ψ : V_{K′} → V is the K₁-linear map with
T_ψ(x ⊗ λ) = ψ(λ)x, and ι_V : V → V_{K′}, x ↦ x ⊗ 1.

Paper statement: "Let V be a normed K₁-space; no nonarchimedean hypothesis is made on V.
(1) ‖T_ψ u‖ ≤ ‖ψ‖ ‖u‖_π for every bounded K₁-linear ψ : K′ → K₁.
(2) ‖·‖_π is a K′-norm on V_{K′}.
(3) ι_V is isometric.
(4) Let V ⊗̂_π K′ be the completion of (V_{K′}, ‖·‖_π). If V is complete, then T_ϖ, with ϖ as
in Corollary D.4, extends to a K₁-linear map Π_V : V ⊗̂_π K′ → V with ‖Π_V‖ ≤ 1 and
Π_V ∘ ι_V = id_V."

Formalization notes:
* `K₁ ⊆ K′` with the restricted absolute value is `NormedAlgebra K₁ K′`. (H1) is
  `NontriviallyNormedField K₁`, `CompleteSpace K₁`, `SphericallyCompleteSpace K₁` (library
  class from `AlternatingAnalytic/Analysis/SphericalCompleteness.lean`, imported for this
  definition only); (H2) is `NormedField K′` with `IsUltrametricDist K′`. The standing
  hypotheses are assumed in all four parts (part (1) does not need them).
* `V_{K′}` is Mathlib's algebraic tensor product `V ⊗[K₁] K′`. The definitions `projNorm`
  (the ordinary-sum projective norm as an infimum over lists of pairs), `contraction` (`T_ψ`,
  defined as `rid ∘ (ψ ⊗ id)`, i.e. `x ⊗ λ ↦ ψ(λ) • x`) and `scaleRight` (the `K′`-action
  `x ⊗ λ ↦ x ⊗ μλ` through the second factor) are introduced in this file. `ι_V x` is written
  `x ⊗ₜ 1`.
* (1): ψ is a continuous `K₁`-linear map `K′ →L[K₁] K₁` with operator norm `‖ψ‖`.
* (2): "a K′-norm" is spelled out as nonnegativity, definiteness (`= 0 ↔ u = 0`), the
  triangle inequality and `‖μ u‖_π = |μ| ‖u‖_π` for the second-factor action.
* (4): ϖ is "as in Corollary D.4": a `K₁`-linear map with `ϖ|K₁ = id` and `|ϖ λ| ≤ |λ|`.
  The completion `V ⊗̂_π K′` is not constructed (the file has no normed-group structure on
  `V ⊗[K₁] K′`, which would need (2)); instead the statement quantifies over every completion
  in the universal sense: a complete normed `K₁`-space `W` with a `K₁`-linear `j` that is
  `‖·‖_π`-isometric with dense range. "Π_V extends T_ϖ" is `Π (j u) = T_ϖ u`, and
  "Π_V ∘ ι_V = id" is `Π (j (x ⊗ 1)) = x`. Only the `K₁`-structure of the completion is used;
  its `K′`-structure is not part of the statement.
* `V` and `K′` lie in the same universe `u` (the library's base-change construction requires
  this); `K₁` and `W` have independent universes.
-/

open scoped TensorProduct

namespace AlternatingAnalyticChallenge.LemD_6

universe u₁ u uW

section Definitions

variable (K₁ : Type u₁) (V K' : Type u) [NontriviallyNormedField K₁]
  [NormedAddCommGroup V] [NormedSpace K₁ V] [NormedField K'] [NormedAlgebra K₁ K']

/-- The projective norm `‖u‖_π = inf { ∑ⱼ ‖xⱼ‖ |λⱼ| : u = ∑ⱼ xⱼ ⊗ λⱼ }` on `V_{K′} = V ⊗_{K₁} K′`,
the infimum over finite decompositions (lists of pairs), with an ordinary sum. -/
noncomputable def projNorm (u : V ⊗[K₁] K') : ℝ :=
  ⨅ s : {s : List (V × K') // (s.map fun z => z.1 ⊗ₜ[K₁] z.2).sum = u},
    (s.val.map fun z => ‖z.1‖ * ‖z.2‖).sum

variable {K₁ V K'}

/-- `T_ψ : V_{K′} → V`, the `K₁`-linear map with `T_ψ (x ⊗ λ) = ψ(λ) x`. -/
noncomputable def contraction (ψ : K' →ₗ[K₁] K₁) : V ⊗[K₁] K' →ₗ[K₁] V :=
  (TensorProduct.rid K₁ V).toLinearMap.comp (ψ.lTensor V)

variable (V)

/-- Multiplication by `μ ∈ K′` on `V_{K′}` through the second factor:
`x ⊗ λ ↦ x ⊗ μλ`. This is the `K′`-vector space structure of `V_{K′}`. -/
noncomputable def scaleRight (μ : K') : V ⊗[K₁] K' →ₗ[K₁] V ⊗[K₁] K' :=
  (LinearMap.mulLeft K₁ μ).lTensor V

end Definitions

variable {K₁ : Type u₁} {V K' : Type u} [NontriviallyNormedField K₁] [CompleteSpace K₁]
  [SphericallyCompleteSpace K₁] [NormedAddCommGroup V] [NormedSpace K₁ V]
  [NormedField K'] [NormedAlgebra K₁ K'] [IsUltrametricDist K']

/-- **Lemma D.6(1).** `‖T_ψ u‖ ≤ ‖ψ‖ ‖u‖_π` for every bounded `K₁`-linear `ψ : K′ → K₁`. -/
theorem part1 (ψ : K' →L[K₁] K₁) (u : V ⊗[K₁] K') :
    ‖contraction ψ.toLinearMap u‖ ≤ ‖ψ‖ * projNorm K₁ V K' u := by
  sorry

/-- **Lemma D.6(2).** `‖·‖_π` is a `K′`-norm on `V_{K′}`: nonnegative, zero only at zero,
subadditive, and absolutely homogeneous for the `K′`-action through the second factor. -/
theorem part2 :
    (∀ u : V ⊗[K₁] K', 0 ≤ projNorm K₁ V K' u) ∧
      (∀ u : V ⊗[K₁] K', projNorm K₁ V K' u = 0 ↔ u = 0) ∧
      (∀ u v : V ⊗[K₁] K', projNorm K₁ V K' (u + v) ≤ projNorm K₁ V K' u + projNorm K₁ V K' v) ∧
      ∀ (μ : K') (u : V ⊗[K₁] K'),
        projNorm K₁ V K' (scaleRight V μ u) = ‖μ‖ * projNorm K₁ V K' u := by
  sorry

/-- **Lemma D.6(3).** `ι_V : x ↦ x ⊗ 1` is isometric. -/
theorem part3 (x : V) : projNorm K₁ V K' (x ⊗ₜ[K₁] (1 : K')) = ‖x‖ := by
  sorry

/-- **Lemma D.6(4).** If `V` is complete and `ϖ` is as in Corollary D.4, then `T_ϖ` extends to
a `K₁`-linear map `Π_V` on the completion `V ⊗̂_π K′` with `‖Π_V‖ ≤ 1` and `Π_V ∘ ι_V = id`.
The completion is given by its universal description: a complete normed `K₁`-space `W` with a
`K₁`-linear map `j : V_{K′} → W` that is isometric for `‖·‖_π` and has dense range. -/
theorem part4 [CompleteSpace V]
    (ϖ : K' →ₗ[K₁] K₁) (hϖfix : ∀ c : K₁, ϖ (algebraMap K₁ K' c) = c)
    (hϖle : ∀ l : K', ‖ϖ l‖ ≤ ‖l‖)
    {W : Type uW} [NormedAddCommGroup W] [NormedSpace K₁ W] [CompleteSpace W]
    (j : V ⊗[K₁] K' →ₗ[K₁] W) (hj : ∀ u, ‖j u‖ = projNorm K₁ V K' u) (hjd : DenseRange j) :
    ∃ P : W →L[K₁] V, ‖P‖ ≤ 1 ∧ (∀ u, P (j u) = contraction ϖ u) ∧
      ∀ x : V, P (j (x ⊗ₜ[K₁] (1 : K'))) = x := by
  sorry

end AlternatingAnalyticChallenge.LemD_6
