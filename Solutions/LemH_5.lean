import AlternatingAnalytic.Analysis.RationalLaurentScalars
import AlternatingAnalytic.Analysis.RigidDenseSource

/-!
# Proof of Lemma H.5

Uses `AlternatingAnalytic.RigidDenseSource.existsUnique_scalar` and
`AlternatingAnalytic.RigidDenseSource.dual_eq_zero`
(`AlternatingAnalytic/Analysis/RigidDenseSourceGeneric.lean`), with density from
`AlternatingAnalytic.RationalField.denseRange_algebraMap`.
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
  have : Nonempty (Fin p) := ⟨⟨0, (Fact.out : p.Prime).pos⟩⟩
  obtain ⟨s, hs, -⟩ := AlternatingAnalytic.RigidDenseSource.existsUnique_scalar
    (AlternatingAnalytic.RationalField.denseRange_algebraMap (ZMod p) r) ha T
  exact ⟨s, hs⟩

/-- Lemma H.5, second assertion: every bounded linear map `E → K` is zero. -/
theorem part2 (p : ℕ) [Fact p.Prime] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)]
    (a : Fin p → AlternatingAnalytic.LaurentField (ZMod p) r)
    (ha : AlgebraicIndependent (AlternatingAnalytic.RationalField (ZMod p) r) a)
    (f : sourceE (AlternatingAnalytic.RationalField (ZMod p) r) a
      →L[AlternatingAnalytic.RationalField (ZMod p) r]
        AlternatingAnalytic.RationalField (ZMod p) r) :
    f = 0 := by
  have : Nonempty (Fin p) := ⟨⟨0, (Fact.out : p.Prime).pos⟩⟩
  exact AlternatingAnalytic.RigidDenseSource.dual_eq_zero
    (AlternatingAnalytic.RationalField.denseRange_algebraMap (ZMod p) r) ha f

end AlternatingAnalyticChallenge.LemH_5
