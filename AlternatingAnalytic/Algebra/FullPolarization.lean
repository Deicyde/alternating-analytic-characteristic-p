import AlternatingAnalytic.Algebra.PolynomialIdentity
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.Algebra.Module.BigOperators

/-!
# Full polarization over an infinite field

The coefficients of the diagonal of a multilinear map are the actual sums
of its values over coordinate selections with fixed fiber cardinalities.
The vector-valued polynomial identity principle therefore recovers every
such sum from the diagonal over an infinite field. No factorial is divided
out, and no symmetry or alternation is assumed.
-/

noncomputable section

namespace Polarization

variable {J : Type*} [Fintype J] {k : ℕ}

/-- The multiplicity of each label in a coordinate selection map. -/
def selectionType (f : Fin k → J) (j : J) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => f i = j)).card

/-- The same actual multiplicities as a finitely supported polynomial exponent. -/
def selectionMultiIndex (f : Fin k → J) : J →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (selectionType f)

@[simp]
theorem selectionMultiIndex_apply (f : Fin k → J) (j : J) :
    selectionMultiIndex f j = selectionType f j := by
  simp [selectionMultiIndex]

@[simp]
theorem selectionMultiIndex_eq_iff (f : Fin k → J) (α : J → ℕ) :
    selectionMultiIndex f = Finsupp.equivFunOnFinite.symm α ↔ selectionType f = α := by
  exact Finsupp.equivFunOnFinite.symm.injective.eq_iff

/-- Every coordinate is counted exactly once. -/
theorem sum_selectionType (f : Fin k → J) : ∑ j, selectionType f j = k := by
  classical
  simpa [selectionType] using
    (Finset.sum_fiberwise' (Finset.univ : Finset (Fin k)) f (fun _ => (1 : ℕ)))

/-- The monomial indexed by a selection type is the product of its selected scalars. -/
theorem monomial_selectionMultiIndex {K : Type*} [CommMonoid K]
    (f : Fin k → J) (t : J → K) :
    (selectionMultiIndex f).prod (fun j n => t j ^ n) = ∏ i, t (f i) := by
  classical
  rw [Finsupp.prod_pow]
  simpa [selectionType] using
    (Finset.prod_fiberwise' (Finset.univ : Finset (Fin k)) f t)

end Polarization

namespace MultilinearMap

variable {K A Y J : Type*} [Field K]
  [AddCommGroup A] [Module K A] [AddCommGroup Y] [Module K Y]
  [Fintype J] {k : ℕ}

open scoped Classical

/-- The genuine filtered sum over coordinate selections of the prescribed type. -/
def sumOfType (M : MultilinearMap K (fun _ : Fin k => A) Y)
    (b : J → A) (α : J → ℕ) : Y := by
  classical
  exact ∑ f ∈ Finset.univ.filter (fun f : Fin k → J => Polarization.selectionType f = α),
    M (fun i => b (f i))

/-- The actual finitely supported coefficients obtained by grouping all
multilinear expansion terms by their multiplicity multi-index. -/
def diagonalCoefficients (M : MultilinearMap K (fun _ : Fin k => A) Y)
    (b : J → A) : (J →₀ ℕ) →₀ Y := by
  classical
  exact ∑ f : Fin k → J,
    Finsupp.single (Polarization.selectionMultiIndex f) (M (fun i => b (f i)))

/-- A coefficient is exactly its fixed-type filtered sum, with no assumed
coefficient identity. -/
theorem diagonalCoefficients_apply (M : MultilinearMap K (fun _ : Fin k => A) Y)
    (b : J → A) (α : J → ℕ) :
    M.diagonalCoefficients b (Finsupp.equivFunOnFinite.symm α) = M.sumOfType b α := by
  classical
  simp only [diagonalCoefficients, Finsupp.finsetSum_apply, Finsupp.single_apply,
    Polarization.selectionMultiIndex_eq_iff, sumOfType, Finset.sum_filter]

/-- Evaluation of the constructed coefficient family is the original multilinear
diagonal at the genuine weighted sum of the supplied vectors. -/
theorem eval_diagonalCoefficients (M : MultilinearMap K (fun _ : Fin k => A) Y)
    (b : J → A) (t : J → K) :
    VectorPolynomial.eval (M.diagonalCoefficients b) t = M (fun _ => ∑ j, t j • b j) := by
  classical
  unfold VectorPolynomial.eval diagonalCoefficients
  rw [← Finsupp.sum_finsetSum_index (fun _ => smul_zero _)
    (fun _ _ _ => smul_add _ _ _)]
  simp only [Finsupp.sum_single_index, smul_zero, Polarization.monomial_selectionMultiIndex]
  rw [M.map_sum]
  exact Finset.sum_congr rfl fun f _ => (M.map_smul_univ _ _).symm

/-- Multilinearity makes the coefficient family homogeneous of degree k. -/
theorem sumOfType_eq_zero_of_sum_ne (M : MultilinearMap K (fun _ : Fin k => A) Y)
    (b : J → A) (α : J → ℕ) (hα : ∑ j, α j ≠ k) : M.sumOfType b α = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro f hf
  have h := (Finset.mem_filter.mp hf).2
  exact False.elim (hα (h ▸ Polarization.sum_selectionType f))

/-- Full polarization over an infinite field: equality of diagonals forces equality
of every grouped coefficient. The label type may be any finite type, and the
requested multiplicity function need not be pre-assumed to sum to k. -/
theorem sumOfType_eq_of_diagonal_eq [Infinite K]
    (M N : MultilinearMap K (fun _ : Fin k => A) Y)
    (h : ∀ a : A, M (fun _ => a) = N (fun _ => a))
    (b : J → A) (α : J → ℕ) : M.sumOfType b α = N.sumOfType b α := by
  classical
  have hz := VectorPolynomial.coeff_eq_zero_of_eval_eq_zero (K := K)
    ((M - N).diagonalCoefficients b) (fun t => by
      rw [eval_diagonalCoefficients]
      exact sub_eq_zero.mpr (h _)) (Finsupp.equivFunOnFinite.symm α)
  rw [diagonalCoefficients_apply] at hz
  apply sub_eq_zero.mp
  simpa only [sumOfType, sub_apply, Finset.sum_sub_distrib] using hz

/-- A one-label grouped coefficient is the original diagonal value. -/
@[simp]
theorem sumOfType_unit (M : MultilinearMap K (fun _ : Fin k => A) Y) (a : A) :
    M.sumOfType (fun _ : Unit => a) (fun _ => k) = M (fun _ => a) := by
  classical
  have htype (f : Fin k → Unit) : Polarization.selectionType f = fun _ => k := by
    funext j
    simp [Polarization.selectionType]
  simp [sumOfType, htype]

/-- The one-label case of the full polarized identity gives the pointwise diagonal,
over every field. -/
theorem diagonal_eq_of_sumOfType_eq
    (M N : MultilinearMap K (fun _ : Fin k => A) Y)
    (h : ∀ (b : Unit → A) (α : Unit → ℕ), M.sumOfType b α = N.sumOfType b α)
    (a : A) : M (fun _ => a) = N (fun _ => a) := by
  simpa only [sumOfType_unit] using h (fun _ => a) (fun _ => k)

/-- Apply an additive map only after full polarization over the infinite field.
In particular, the map need not be linear over that infinite field. -/
theorem map_sumOfType_eq_of_diagonal_eq [Infinite K]
    {Z : Type*} [AddCommMonoid Z] (η : Y →+ Z)
    (M N : MultilinearMap K (fun _ : Fin k => A) Y)
    (h : ∀ a : A, M (fun _ => a) = N (fun _ => a))
    (b : J → A) (α : J → ℕ) :
    (∑ f ∈ Finset.univ.filter (fun f : Fin k → J => Polarization.selectionType f = α),
      η (M (fun i => b (f i)))) =
    ∑ f ∈ Finset.univ.filter (fun f : Fin k → J => Polarization.selectionType f = α),
      η (N (fun i => b (f i))) := by
  classical
  simpa only [sumOfType, _root_.map_sum] using congrArg η (sumOfType_eq_of_diagonal_eq M N h b α)

/-- Specialization to the actual multilinear wedge expression for a linear
family of operators. Fixing vector arguments requires no alternation hypothesis. -/
theorem sumOfType_eq_of_multiplier_diagonal [Infinite K]
    {V : Type*} [AddCommGroup V] [Module K V]
    (M : MultilinearMap K (fun _ : Fin k => A) Y)
    (W : MultilinearMap K (fun _ : Fin k => V) Y)
    (D : A →ₗ[K] (V →ₗ[K] V)) (x : Fin k → V)
    (h : ∀ a : A, M (fun _ => a) = W (fun i => D a (x i)))
    (b : J → A) (α : J → ℕ) :
    M.sumOfType b α =
    ∑ f ∈ Finset.univ.filter (fun f : Fin k → J => Polarization.selectionType f = α),
      W (fun i => D (b (f i)) (x i)) := by
  classical
  let N := W.compLinearMap fun i => (LinearMap.applyₗ (R := K) (x i)).comp D
  exact sumOfType_eq_of_diagonal_eq M N h b α


end MultilinearMap
