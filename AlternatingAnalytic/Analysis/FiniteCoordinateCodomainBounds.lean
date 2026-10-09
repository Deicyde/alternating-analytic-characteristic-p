import AlternatingAnalytic.Analysis.FiniteCoordinateDeterminant
import AlternatingAnalytic.Analysis.LiftCriterion
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Norm bounds for the codomain determinant lift

The triangle-inequality bound for the determinant lift of Proposition 4.1(2), with an
explicit real constant `finiteCoordinateCodomainBound`.
-/

noncomputable section

namespace AlternatingAnalytic

open scoped BigOperators
open Module

variable {K E E' F : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup E'] [NormedSpace K E']
  [NormedAddCommGroup F] [NormedSpace K F]
  {d : ℕ}

/-- A coordinate functional of `b`, as a continuous linear map. -/
def finiteCoordinateCodomainFunctional (b : Basis (Fin d) K E')
    (hb : ∀ i, Continuous (b.coord i)) (i : Fin d) : E' →L[K] K :=
  ⟨b.coord i, hb i⟩

@[simp] theorem finiteCoordinateCodomainFunctional_apply (b : Basis (Fin d) K E')
    (hb : ∀ i, Continuous (b.coord i)) (i : Fin d) (x : E') :
    finiteCoordinateCodomainFunctional b hb i x = b.coord i x := rfl

/-- The norm constant of the codomain determinant lift. -/
def finiteCoordinateCodomainBound (b : Basis (Fin d) K E')
    (hb : ∀ i, Continuous (b.coord i)) (k : ℕ) : ℝ :=
  (k.factorial : ℝ) * ∑ s : Set.powersetCard (Fin d) k,
    ∏ a : Fin k,
      (‖finiteCoordinateCodomainFunctional b hb (Set.powersetCard.ofFinEmbEquiv.symm s a)‖ *
        ‖b (Set.powersetCard.ofFinEmbEquiv.symm s a)‖)

theorem finiteCoordinateCodomainBound_nonneg (b : Basis (Fin d) K E')
    (hb : ∀ i, Continuous (b.coord i)) (k : ℕ) :
    0 ≤ finiteCoordinateCodomainBound b hb k := by
  unfold finiteCoordinateCodomainBound
  positivity

/-- The triangle-inequality bound, with a separate operator in each row. -/
theorem norm_finiteCoordinateCodomain_sum_le (b : Basis (Fin d) K E')
    (hb : ∀ i, Continuous (b.coord i)) (k : ℕ)
    (f : Fin k → E →L[K] E') (m : E' [⋀^Fin k]→L[K] F) (x : Fin k → E) :
    ‖∑ s : Set.powersetCard (Fin d) k,
      (Matrix.of fun a j => b.coord (Set.powersetCard.ofFinEmbEquiv.symm s a)
        (f a (x j))).det • m (fun a => b (Set.powersetCard.ofFinEmbEquiv.symm s a))‖ ≤
      finiteCoordinateCodomainBound b hb k * ‖m‖ * (∏ a, ‖f a‖) * ∏ j, ‖x j‖ := by
  classical
  calc
    _ ≤ ∑ s : Set.powersetCard (Fin d) k,
        ‖(Matrix.of fun a j => b.coord (Set.powersetCard.ofFinEmbEquiv.symm s a)
          (f a (x j))).det • m (fun a => b (Set.powersetCard.ofFinEmbEquiv.symm s a))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ s : Set.powersetCard (Fin d) k,
        (k.factorial : ℝ) *
          (∏ a : Fin k, (‖finiteCoordinateCodomainFunctional b hb
            (Set.powersetCard.ofFinEmbEquiv.symm s a)‖ *
            ‖b (Set.powersetCard.ofFinEmbEquiv.symm s a)‖)) *
          ‖m‖ * (∏ a, ‖f a‖) * ∏ j, ‖x j‖ := by
      apply Finset.sum_le_sum
      intro s _
      let t := Set.powersetCard.ofFinEmbEquiv.symm s
      have hdet := norm_det_le_factorial_mul_prod
        (Matrix.of fun a j => finiteCoordinateCodomainFunctional b hb (t a) (f a (x j)))
        (fun a => ‖finiteCoordinateCodomainFunctional b hb (t a)‖ * ‖f a‖)
        (fun j => ‖x j‖)
        (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) (fun _ => norm_nonneg _)
        (fun a j => calc
          _ ≤ ‖finiteCoordinateCodomainFunctional b hb (t a)‖ * ‖f a (x j)‖ :=
            (finiteCoordinateCodomainFunctional b hb (t a)).le_opNorm _
          _ ≤ ‖finiteCoordinateCodomainFunctional b hb (t a)‖ * (‖f a‖ * ‖x j‖) :=
            mul_le_mul_of_nonneg_left ((f a).le_opNorm _) (norm_nonneg _)
          _ = _ := (mul_assoc _ _ _).symm)
      rw [norm_smul]
      calc
        _ ≤ ((k.factorial : ℝ) *
            (∏ a, ‖finiteCoordinateCodomainFunctional b hb (t a)‖ * ‖f a‖) *
            ∏ j, ‖x j‖) * (‖m‖ * ∏ a, ‖b (t a)‖) :=
          mul_le_mul hdet (m.le_opNorm _) (norm_nonneg _) (by positivity)
        _ = _ := by simp only [Finset.prod_mul_distrib]; ring
    _ = _ := by
      simp only [finiteCoordinateCodomainBound, Finset.sum_mul, Finset.mul_sum]

/-- There are no `k`-element subsets of `Fin d` when `d < k`. -/
theorem finiteCoordinateCodomainIndices_isEmpty {d k : ℕ} (h : d < k) :
    IsEmpty (Set.powersetCard (Fin d) k) := by
  refine ⟨fun s => ?_⟩
  have hs : k ≤ d := by
    have hc := Finset.card_le_univ s.val
    simpa only [Set.powersetCard.card_eq, Fintype.card_fin] using hc
  omega

theorem finiteCoordinateCodomainBound_eq_zero_of_lt (b : Basis (Fin d) K E')
    (hb : ∀ i, Continuous (b.coord i)) {k : ℕ} (h : d < k) :
    finiteCoordinateCodomainBound b hb k = 0 := by
  let := finiteCoordinateCodomainIndices_isEmpty h
  simp [finiteCoordinateCodomainBound]

theorem finiteCoordinateCodomainBound_zero (b : Basis (Fin d) K E')
    (hb : ∀ i, Continuous (b.coord i)) : finiteCoordinateCodomainBound b hb 0 = 1 := by
  let : Unique (Set.powersetCard (Fin d) 0) :=
    ⟨⟨∅, rfl⟩, fun s => Subtype.ext (Finset.card_eq_zero.mp s.prop)⟩
  simp [finiteCoordinateCodomainBound]

end AlternatingAnalytic
