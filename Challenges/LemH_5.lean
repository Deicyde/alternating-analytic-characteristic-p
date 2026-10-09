import AlternatingAnalytic.Analysis.RationalLaurentScalars

/-!
# Lemma H.5 (rigidity of the source `E`), p. 61

Setting (Appendix H.1): `p` is prime, `K = 𝔽_p(t)` with its `t`-adic absolute value and
`L = 𝔽_p((t))` its completion. `A = L[ε]/(ε^p)` with basis `e_i = ε^i` (`0 ≤ i < p`) carries
"the maximum norm in this basis". "Choose elements `a_0, …, a_{p-1} ∈ L`, together with the
finitely many auxiliary scalars `τ_w` introduced below, algebraically independent over `K`. … Set
`a = ∑_{i<p} a_i e_i`, `E = K^p + K a ⊆ A`. Every subspace used below carries the norm induced by
`A` or `L`."

Paper statement: "Every bounded endomorphism of `E` is multiplication by a scalar in `K`, and
every bounded linear map `E → K` is zero."

## Formalization notes

* `K` and `L` are the library's `AlternatingAnalytic.RationalField (ZMod p) r` and
  `AlternatingAnalytic.LaurentField (ZMod p) r`, with the `t`-adic norm `‖t‖ = r` for
  `0 < r < 1`.
* Only the normed `K`-space structure of `A` is used, so `A` is modelled as `Fin p → L` with the
  sup norm, the maximum norm in the basis `e_i`. `K^p ⊆ A` is the range of
  `coordinateInclusion`, and `sourceE K L a` is `K^p + K a` with the induced norm.
* Only the algebraic independence of `a_0, …, a_{p-1}` over `K` is assumed. The paper's
  hypothesis (joint independence with the `τ_w`) implies it, so the Lean statement is at least
  as strong.
-/

namespace AlternatingAnalyticChallenge.LemH_5

open scoped NNReal

section Definitions

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- The coordinatewise inclusion `K^n → L^n`. -/
def coordinateInclusion (I : Type*) : (I → K) →ₗ[K] (I → L) where
  toFun b i := algebraMap K L (b i)
  map_add' b c := by ext i; simp
  map_smul' s b := by ext i; simp [Algebra.smul_def]

variable {L}

/-- The source `E = K^p + K a`, as a `K`-submodule of the coordinate space `Fin p → L ≅ A`. -/
def sourceE {p : ℕ} (a : Fin p → L) : Submodule K (Fin p → L) :=
  LinearMap.range (coordinateInclusion K L (Fin p)) ⊔ K ∙ a

end Definitions

/-- Lemma H.5, first assertion: every bounded endomorphism of `E = K^p + K a` is
multiplication by a scalar in `K`. -/
theorem part1 (p : ℕ) [Fact p.Prime] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)]
    (a : Fin p → AlternatingAnalytic.LaurentField (ZMod p) r)
    (ha : AlgebraicIndependent (AlternatingAnalytic.RationalField (ZMod p) r) a)
    (T : sourceE (AlternatingAnalytic.RationalField (ZMod p) r) a
      →L[AlternatingAnalytic.RationalField (ZMod p) r]
        sourceE (AlternatingAnalytic.RationalField (ZMod p) r) a) :
    ∃ s : AlternatingAnalytic.RationalField (ZMod p) r, ∀ x, T x = s • x := by
  sorry

/-- Lemma H.5, second assertion: every bounded linear map `E → K` is zero. -/
theorem part2 (p : ℕ) [Fact p.Prime] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)]
    (a : Fin p → AlternatingAnalytic.LaurentField (ZMod p) r)
    (ha : AlgebraicIndependent (AlternatingAnalytic.RationalField (ZMod p) r) a)
    (f : sourceE (AlternatingAnalytic.RationalField (ZMod p) r) a
      →L[AlternatingAnalytic.RationalField (ZMod p) r]
        AlternatingAnalytic.RationalField (ZMod p) r) :
    f = 0 := by
  sorry

end AlternatingAnalyticChallenge.LemH_5
