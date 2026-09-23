import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Finite staircase matrices

Over every field, a square matrix equal to `a` on and above the diagonal and to
`b` below it has rank at least its size minus one if `a ≠ b`. This is the finite
rank calculation in the cluster staircase argument; constructing that matrix
from a hypothetical multiplier lift is a separate step.
-/

namespace AlternatingAnalytic

variable {L : Type*} [Field L]

/-- The two-letter square staircase matrix. -/
def staircaseMatrix (a b : L) (n : ℕ) : Matrix (Fin n) (Fin n) L :=
  fun i j => if i ≤ j then a else b

/-- Rank is subadditive under matrix subtraction. -/
theorem matrix_rank_sub_le {m n : Type*} [Fintype m] [Fintype n]
    (A B : Matrix m n L) : (A - B).rank ≤ A.rank + B.rank := by
  classical
  calc
    (A - B).rank ≤ Module.finrank L
        (LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin : Submodule L (m → L)) := by
      apply Submodule.finrank_mono
      rintro _ ⟨v, rfl⟩
      change (A - B).mulVec v ∈ _
      rw [Matrix.sub_mulVec]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left ⟨v, rfl⟩)
        (Submodule.mem_sup_right ⟨v, rfl⟩)
    _ ≤ A.rank + B.rank := Submodule.finrank_add_le_finrank_add_finrank _ _

/-- Subtracting the constant lower letter gives an upper triangular determinant. -/
theorem det_staircaseMatrix_sub_constant (a b : L) (n : ℕ) :
    (staircaseMatrix a b n - (Matrix.of fun _ _ : Fin n => b)).det = (a - b) ^ n := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [staircaseMatrix, Matrix.sub_apply]
  · intro i j hij
    change j < i at hij
    change (if i ≤ j then a else b) - b = 0
    rw [ite_eq_right (not_le.mpr hij), sub_self]

/-- A staircase with distinct letters has rank at least its size minus one. -/
theorem staircaseMatrix_size_le_rank_add_one (a b : L) (hab : a ≠ b) (n : ℕ) :
    n ≤ (staircaseMatrix a b n).rank + 1 := by
  let C : Matrix (Fin n) (Fin n) L := Matrix.of fun _ _ => b
  have hC : C.rank ≤ 1 := by
    have h : C = Matrix.vecMulVec (fun _ : Fin n => b) (fun _ : Fin n => (1 : L)) := by
      ext i j
      simp [C, Matrix.vecMulVec]
    rw [h]
    exact Matrix.rank_vecMulVec_le _ _
  have hdet : (staircaseMatrix a b n - C).det ≠ 0 := by
    rw [det_staircaseMatrix_sub_constant]
    exact pow_ne_zero _ (sub_ne_zero.mpr hab)
  have hfull : (staircaseMatrix a b n - C).rank = n := by
    simpa using Matrix.rank_of_det_ne_zero hdet
  calc
    n = (staircaseMatrix a b n - C).rank := hfull.symm
    _ ≤ (staircaseMatrix a b n).rank + C.rank := matrix_rank_sub_le _ _
    _ ≤ (staircaseMatrix a b n).rank + 1 := Nat.add_le_add_left hC _

/-- The size `d + 2` staircase of rank at most `d` must have equal letters. -/
theorem staircaseMatrix_letters_eq_of_rank_le (a b : L) (d : ℕ)
    (h : (staircaseMatrix a b (d + 2)).rank ≤ d) : a = b := by
  by_contra hab
  have := staircaseMatrix_size_le_rank_add_one a b hab (d + 2)
  omega

end AlternatingAnalytic
