import AlternatingAnalytic.Scalar.ChainSpaces.Main
import AlternatingAnalytic.Scalar.Tails.LpTails
import AlternatingAnalytic.Scalar.TestCertificate.Certificate
import AlternatingAnalytic.Scalar.FibreObstruction

/-!
# Theorem F.1, unconditionally

The two hypotheses of `sequenceConclusion_of_lemmas` are discharged by the library:
`MultilinearDiagonalTail` by Lemma F.2, part 3 (`AlternatingAnalytic.Tails`), and
`FiniteTestCertificate` by Lemma F.5 (`AlternatingAnalytic.TestCertificate`, by duality over
`ZMod p`) applied to Lemma F.4 over `ZMod p` (`AlternatingAnalytic.FibreObstruction`).
-/

set_option maxSynthPendingDepth 2

namespace AlternatingAnalytic.ChainSpaces

universe u

/-- Lemma F.2, part 3, in the form used by Theorem F.1. -/
theorem multilinearDiagonalTail (K : Type u) [NontriviallyNormedField K] [CompleteSpace K] :
    MultilinearDiagonalTail K := by
  intro _ hK I _ _ _ d hd μ
  exact AlternatingAnalytic.Tails.multilinear_diagonal_tendsto_zero hK hd μ

/-- Lemma F.5 (from Lemma F.4 over `ZMod p`), in the form used by Theorem F.1. -/
theorem finiteTestCertificate (K : Type u) [NormedField K] (k : ℕ) : FiniteTestCertificate K k :=
  fun hk => AlternatingAnalytic.TestCertificate.exists_finite_test_certificate_of_fibre K k hk
    fun _ _ hp => AlternatingAnalytic.FibreObstruction.not_exists_fibre_map hp

/-- **Theorem F.1, part 2 (sequence-space form).** -/
theorem sequenceConclusion (K : Type u) [NontriviallyNormedField K] [CompleteSpace K]
    (hK : ¬ SphericallyCompleteSpace K) (k : ℕ) (hk : (k.factorial : K) = 0) :
    SequenceConclusion K k :=
  sequenceConclusion_of_lemmas K hK k hk (multilinearDiagonalTail K) (finiteTestCertificate K k)

/-- **Theorem F.1, part 1 (abstract form).** -/
theorem abstractConclusion (K : Type u) [NontriviallyNormedField K] [CompleteSpace K]
    (hK : ¬ SphericallyCompleteSpace K) (k : ℕ) (hk : (k.factorial : K) = 0) :
    AbstractConclusion K k :=
  abstractConclusion_of_lemmas K hK k hk (multilinearDiagonalTail K) (finiteTestCertificate K k)

end AlternatingAnalytic.ChainSpaces
