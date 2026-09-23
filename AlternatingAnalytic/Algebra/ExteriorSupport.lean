import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Exterior antisymmetrization

Exterior basis coordinates factor through antisymmetrization into the tensor power.
Consequently antisymmetrization is injective over every field, in every degree and
characteristic.
-/

namespace AlternatingAnalytic

/-- Antisymmetrization into the tensor power is injective over any field, including
when the degree factorial vanishes in the field. -/
theorem toTensorPower_injective
    (L : Type*) [Field L] (V : Type*) [AddCommGroup V] [Module L V] (k : ℕ) :
    Function.Injective (exteriorPower.toTensorPower L V k) := by
  classical
  let : LinearOrder (Module.Free.ChooseBasisIndex L V) := linearOrderOfSTO WellOrderingRel
  let b := Module.Free.chooseBasis L V
  intro x y h
  apply (b.exteriorPower k).ext_elem
  intro s
  simp only [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual,
    exteriorPower.ιMulti_family, exteriorPower.pairingDual,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  exact congrArg (TensorPower.multilinearMapToDual L V k
    (b.coord ∘ Set.powersetCard.ofFinEmbEquiv.symm s)) h

end AlternatingAnalytic
