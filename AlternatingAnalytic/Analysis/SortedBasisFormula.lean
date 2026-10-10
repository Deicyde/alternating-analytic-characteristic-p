import AlternatingAnalytic.Analysis.SortedBasisAnalytic
import AlternatingAnalytic.Analysis.SortedBasisExpansion

/-!
# Determinant formula for the sorted lift

For an unconditional Schauder basis with `‖b.coord i x‖ * ‖b i‖ ≤ ‖x‖` and a complete
ultrametric target, the sorted lift `sortedSchauderLift` is given by a convergent sum over
increasing index tuples of determinants of coordinates. This is the infinite analogue of the
finite-coordinate formula in the proof of Proposition 4.1.
-/

noncomputable section

namespace AlternatingAnalytic

open scoped BigOperators

variable {K I E E' F : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [LinearOrder I] [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup E'] [NormedSpace K E']
  [NormedAddCommGroup F] [NormedSpace K F] [IsUltrametricDist F] [CompleteSpace F]

/-- The sorted determinant family sums to the sorted lift. -/
theorem hasSum_sortedSchauderLift (b : UnconditionalSchauderBasis I K E)
    (hb : ∀ i x, ‖b.coord i x‖ * ‖b i‖ ≤ ‖x‖) (n : ℕ)
    (f : Fin n → E →L[K] E') (m : E' [⋀^Fin n]→L[K] F) (x : Fin n → E) :
    HasSum (fun s : Set.powersetCard I n =>
      (Matrix.of fun i j => b.coord (Set.powersetCard.ofFinEmbEquiv.symm s i) (x j)).det •
        m (fun i => f i (b (Set.powersetCard.ofFinEmbEquiv.symm s i))))
      (sortedSchauderLift b hb n f m x) := by
  have h := hasSum_sortedBasisTerm b n (sortedSchauderLift b hb n f m) x
  convert h using 1
  ext s
  simp only [sortedBasisTerm, ContinuousAlternatingMap.coe_toContinuousMultilinearMap,
    sortedSchauderLift_basis]

/-- The sorted lift equals the sum of the sorted determinant family. -/
theorem sortedSchauderLift_eq_tsum (b : UnconditionalSchauderBasis I K E)
    (hb : ∀ i x, ‖b.coord i x‖ * ‖b i‖ ≤ ‖x‖) (n : ℕ)
    (f : Fin n → E →L[K] E') (m : E' [⋀^Fin n]→L[K] F) (x : Fin n → E) :
    sortedSchauderLift b hb n f m x =
      ∑' s : Set.powersetCard I n,
        (Matrix.of fun i j => b.coord (Set.powersetCard.ofFinEmbEquiv.symm s i) (x j)).det •
          m (fun i => f i (b (Set.powersetCard.ofFinEmbEquiv.symm s i))) :=
  (hasSum_sortedSchauderLift b hb n f m x).tsum_eq.symm

noncomputable local instance sortedFormulaLiftNorm (n : ℕ) :
    Norm ((E →L[K] E') [×n]→L[K]
      ((E' [⋀^Fin n]→L[K] F) →L[K] (E [⋀^Fin n]→L[K] F))) :=
  ContinuousMultilinearMap.hasOpNorm
    (𝕜 := K) (E := fun _ : Fin n => E →L[K] E')
    (G := (E' [⋀^Fin n]→L[K] F) →L[K] (E [⋀^Fin n]→L[K] F))

/-- There is a multilinear lift of norm at most one of the precomposition action `Q`,
given by the sorted determinant formula. -/
theorem exists_sortedSchauderLift (b : UnconditionalSchauderBasis I K E)
    (hb : ∀ i x, ‖b.coord i x‖ * ‖b i‖ ≤ ‖x‖) (n : ℕ) :
    ∃ P : (E →L[K] E') [×n]→L[K]
        ((E' [⋀^Fin n]→L[K] F) →L[K] (E [⋀^Fin n]→L[K] F)),
      ‖P‖ ≤ 1 ∧
      (∀ f, P (fun _ => f) = LiftCriterion.Q K (Fin n) E E' F f) ∧
      ∀ (f : Fin n → E →L[K] E') (m : E' [⋀^Fin n]→L[K] F) (x : Fin n → E),
        HasSum (fun s : Set.powersetCard I n =>
          (Matrix.of fun i j => b.coord (Set.powersetCard.ofFinEmbEquiv.symm s i) (x j)).det •
            m (fun i => f i (b (Set.powersetCard.ofFinEmbEquiv.symm s i)))) (P f m x) :=
  ⟨sortedSchauderLift b hb n, norm_sortedSchauderLift_le b hb n,
    sortedSchauderLift_diag b hb n, hasSum_sortedSchauderLift b hb n⟩

end AlternatingAnalytic
