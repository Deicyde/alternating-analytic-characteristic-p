import Mathlib.Algebra.Algebra.Bilinear

/-!
# Sequence multiplication operators

Pointwise multiplication of sequences as a linear map into linear endomorphisms.
-/

namespace AlternatingAnalytic

variable (L : Type*) [Field L]

/-- Send a sequence to the linear operator given by pointwise multiplication by it. -/
def sequenceMultiplier : (ℕ → L) →ₗ[L] Module.End L (ℕ → L) :=
  LinearMap.mul L (ℕ → L)

@[simp]
theorem sequenceMultiplier_apply (a x : ℕ → L) (n : ℕ) :
    sequenceMultiplier L a x n = a n * x n :=
  rfl

end AlternatingAnalytic
