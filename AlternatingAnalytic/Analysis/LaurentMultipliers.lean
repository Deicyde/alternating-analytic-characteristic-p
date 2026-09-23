import AlternatingAnalytic.Analysis.LaurentCoefficients
import Mathlib.Analysis.Normed.Operator.Mul

/-! Bounded pointwise multipliers and the constant coefficient-field embedding. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NNReal BoundedContinuousFunction
namespace AlternatingAnalytic

variable (K : Type*) [NontriviallyNormedField K] (S : Type*) [TopologicalSpace S]

/-- A bounded sequence acts by continuous pointwise multiplication. -/
def boundedSequenceMultiplier : (S →ᵇ K) →L[K] ((S →ᵇ K) →L[K] (S →ᵇ K)) :=
  ContinuousLinearMap.mul K (S →ᵇ K)

@[simp]
theorem boundedSequenceMultiplier_apply (a x : S →ᵇ K) (s : S) :
    boundedSequenceMultiplier K S a x s = a s * x s := rfl

theorem norm_boundedSequenceMultiplier_le (a : S →ᵇ K) :
    ‖boundedSequenceMultiplier K S a‖ ≤ ‖a‖ :=
  ContinuousLinearMap.opNorm_mul_apply_le K (S →ᵇ K) a

variable (κ : Type*) [Field κ] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)]
/-- Restriction of the bounded-function module to the coefficient field. -/
instance laurentBoundedFunctionModule : Module κ (S →ᵇ LaurentField κ r) :=
  Module.compHom _ (algebraMap κ (LaurentField κ r))

instance laurentBoundedFunctionScalarTower :
    IsScalarTower κ (LaurentField κ r) (S →ᵇ LaurentField κ r) :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

instance laurentBoundedFunctionContinuousConstSMul :
    ContinuousConstSMul κ (S →ᵇ LaurentField κ r) where
  continuous_const_smul c := show Continuous
    (fun f : S →ᵇ LaurentField κ r ↦ (algebraMap κ (LaurentField κ r) c) • f) from
      continuous_const_smul _

variable [DiscreteTopology S]

@[simp]
theorem constantLaurentArray_add (a b : S → κ) :
    constantLaurentArray κ r (a + b) = constantLaurentArray κ r a + constantLaurentArray κ r b := by
  ext s
  exact map_add (algebraMap κ (LaurentField κ r)) (a s) (b s)

@[simp]
theorem constantLaurentArray_smul_const (c : κ) (a : S → κ) :
    constantLaurentArray κ r (c • a) =
      (algebraMap κ (LaurentField κ r) c) • constantLaurentArray κ r a := by
  ext s
  exact map_mul (algebraMap κ (LaurentField κ r)) c (a s)

@[simp]
theorem constantLaurentArray_mul (a b : S → κ) :
    constantLaurentArray κ r (a * b) = constantLaurentArray κ r a * constantLaurentArray κ r b := by
  ext s
  exact map_mul (algebraMap κ (LaurentField κ r)) (a s) (b s)

@[simp]
theorem boundedSequenceMultiplier_constant (a x : S → κ) :
    boundedSequenceMultiplier (LaurentField κ r) S (constantLaurentArray κ r a)
      (constantLaurentArray κ r x) = constantLaurentArray κ r (a * x) :=
  (constantLaurentArray_mul S κ r a x).symm

/-- The coefficient-field embedding of all arrays into bounded Laurent arrays is linear. -/
def constantLaurentArrayLinear : (S → κ) →ₗ[κ] (S →ᵇ LaurentField κ r) where
  toFun := constantLaurentArray κ r
  map_add' := constantLaurentArray_add S κ r
  map_smul' c a := constantLaurentArray_smul_const S κ r c a

@[simp]
theorem constantLaurentArrayLinear_apply (a : S → κ) :
    constantLaurentArrayLinear S κ r a = constantLaurentArray κ r a := rfl

end AlternatingAnalytic
