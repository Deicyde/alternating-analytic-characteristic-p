import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import AlternatingAnalytic.Analysis.ProjectiveExterior
import AlternatingAnalytic.Exterior.Representation.Isometry

/-!
# Proof of Proposition 5.1

Uses `ExteriorRepresentation.exists_representation` and `ExteriorRepresentation.exists_naturality`
(`Exterior/Representation/Isometry.lean`), applied to `ProjExteriorPre K k E`.
-/

namespace AlternatingAnalyticChallenge.Prop5_1

universe uK uE uD uF

variable (K : Type uK) [NontriviallyNormedField K] (k : ℕ)

/-- The algebraic exterior power `⋀[K]^k E`, as a type carrying the projective seminorm. -/
def ProjExteriorPre (E : Type uE) [NormedAddCommGroup E] [NormedSpace K E] :
    Type (max uK uE) :=
  ↥(⋀[K]^k E)

variable (E : Type uE) [NormedAddCommGroup E] [NormedSpace K E]

noncomputable instance : AddCommGroup (ProjExteriorPre K k E) :=
  inferInstanceAs (AddCommGroup (⋀[K]^k E))

noncomputable instance : Module K (ProjExteriorPre K k E) :=
  inferInstanceAs (Module K (⋀[K]^k E))

/-- The projective seminorm on the algebraic exterior power. -/
noncomputable instance : SeminormedAddCommGroup (ProjExteriorPre K k E) :=
  AddGroupSeminorm.toSeminormedAddCommGroup (E := ProjExteriorPre K k E)
    (AlternatingAnalytic.projectiveExteriorSeminorm (K := K) (V := E) (k := k)).toAddGroupSeminorm

noncomputable instance : NormedSpace K (ProjExteriorPre K k E) :=
  { (inferInstance : Module K (ProjExteriorPre K k E)) with
    norm_smul_le := fun a z =>
      (map_smul_eq_mul (AlternatingAnalytic.projectiveExteriorSeminorm (K := K) (V := E) (k := k))
        a z).le }

/-- The separated, uncompleted projective exterior power `Λ^k_π E`. -/
abbrev ProjExterior : Type (max uK uE) := SeparationQuotient (ProjExteriorPre K k E)

/-- The universal alternating map `ω_E(x_1, …, x_k) = [x_1 ∧ ⋯ ∧ x_k]`. -/
noncomputable def wedge (x : Fin k → E) : ProjExterior K k E :=
  SeparationQuotient.mk (show ProjExteriorPre K k E from exteriorPower.ιMulti K k x)

/-- Proposition 5.1, representation: `Alt^k(E; F) ≃ L(Λ^k_π E, F)` isometrically, with
`Φ m ∘ ω_E = m`. -/
theorem representation (F : Type uF) [NormedAddCommGroup F] [NormedSpace K F] :
    ∃ Φ : (E [⋀^Fin k]→L[K] F) ≃ₗᵢ[K] (ProjExterior K k E →L[K] F),
      ∀ (m : E [⋀^Fin k]→L[K] F) (x : Fin k → E), Φ m (wedge K k E x) = m x :=
  AlternatingAnalytic.ExteriorRepresentation.exists_representation (X := ProjExteriorPre K k E)
    (LinearEquiv.refl K (⋀[K]^k E)) (fun _ => rfl) F

/-- Proposition 5.1, naturality: under the isometries of `representation`, precomposition by
`u : E →L D` corresponds to precomposition by `Λ^k_π u`. -/
theorem naturality (D : Type uD) [NormedAddCommGroup D] [NormedSpace K D] (u : E →L[K] D) :
    ∃ Λu : ProjExterior K k E →L[K] ProjExterior K k D,
      (∀ x : Fin k → E, Λu (wedge K k E x) = wedge K k D (u ∘ x)) ∧
      ∀ (F : Type uF) [NormedAddCommGroup F] [NormedSpace K F]
        (ΦE : (E [⋀^Fin k]→L[K] F) ≃ₗᵢ[K] (ProjExterior K k E →L[K] F))
        (ΦD : (D [⋀^Fin k]→L[K] F) ≃ₗᵢ[K] (ProjExterior K k D →L[K] F)),
        (∀ (m : E [⋀^Fin k]→L[K] F) (x : Fin k → E), ΦE m (wedge K k E x) = m x) →
        (∀ (m : D [⋀^Fin k]→L[K] F) (x : Fin k → D), ΦD m (wedge K k D x) = m x) →
        ∀ m : D [⋀^Fin k]→L[K] F,
          ΦE (m.compContinuousLinearMap u) = (ΦD m).comp Λu :=
  AlternatingAnalytic.ExteriorRepresentation.exists_naturality (X := ProjExteriorPre K k E)
    (LinearEquiv.refl K (⋀[K]^k E)) (fun _ => rfl) (Y := ProjExteriorPre K k D)
    (LinearEquiv.refl K (⋀[K]^k D)) (fun _ => rfl) u

end AlternatingAnalyticChallenge.Prop5_1
