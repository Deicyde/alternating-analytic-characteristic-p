import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import AlternatingAnalytic.Analysis.ProjectiveExterior

/-!
# Proposition 5.1 (representation), p. 13

Setting (Section 5): for `k ≥ 1` give the algebraic exterior power `Λ^k_K E` the seminorm
`‖z‖_π = inf { Σ_j Π_{a=1}^k ‖x_{ja}‖ : z = Σ_j x_{j1} ∧ ⋯ ∧ x_{jk} }`. "Its quotient by the
zero-seminorm subspace is denoted Λ^k_π E. This is an uncompleted normed space, with universal
alternating map ω_E(x_1, …, x_k) = [x_1 ∧ ⋯ ∧ x_k]. Put Λ^0_π E = K and ω_E() = 1."

Paper statement: "There is a natural linear isometry Alt^k(E; F) ≅ L(Λ^k_π E, F) for every
normed F. Under it, precomposition by u : E → D is precomposition by
Λ^k_π u : Λ^k_π E → Λ^k_π D."

## Formalization notes
* The degree is `Fin k`; `E`, `D`, `F` are normed `K`-spaces, not assumed complete.
* `ProjExteriorPre K k E` is Mathlib's `⋀[K]^k E` with the library seminorm
  `projectiveExteriorSeminorm`, an infimum over weighted decompositions
  `Σ_j a_j x_{j1} ∧ ⋯ ∧ x_{jk}`. For `k ≥ 1` it equals the paper's infimum
  (`projectiveExteriorSeminorm_eq_iInf_wedgeCost`); for `k = 0` it gives `Λ^0_π E = K`.
* `ProjExterior K k E` (`Λ^k_π E`) is the `SeparationQuotient`; `wedge K k E` is `ω_E`.
* The isometry is the existence of `Φ : Alt^k(E; F) ≃ₗᵢ L(Λ^k_π E, F)` with `Φ m ∘ ω_E = m`.
  This determines `Φ`, so naturality in `F` follows.
* Naturality in the source: a bounded `Λ^k_π u` with `Λ^k_π u ∘ ω_E = ω_D ∘ (u, …, u)` and
  `Φ_E (m ∘ (u, …, u)) = Φ_D m ∘ Λ^k_π u`. The bound `‖Λ^k_π u‖ ≤ ‖u‖^k` is not stated.
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
      ∀ (m : E [⋀^Fin k]→L[K] F) (x : Fin k → E), Φ m (wedge K k E x) = m x := by
  sorry

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
          ΦE (m.compContinuousLinearMap u) = (ΦD m).comp Λu := by
  sorry

end AlternatingAnalyticChallenge.Prop5_1
