import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import AlternatingAnalytic.Analysis.BoundedRetractionLift
import AlternatingAnalytic.Analysis.FactorialInvertible
import AlternatingAnalytic.Analysis.FiniteCoordinateDomain
import AlternatingAnalytic.Analysis.FiniteCoordinateCodomain

/-!
# Proof of Proposition 4.1

The main part is `AlternatingAnalytic.contractingRetractionLift` (`SortedBasisLift.lean`,
`BoundedRetractionLift.lean`); (1) applies it to `ContinuousAlternatingMap.altProj`
(`FactorialInvertible.lean`); (2) is `finiteCoordinateDomainLift` and
`finiteCoordinateCodomainLift` (`FiniteCoordinateDomain.lean`, `FiniteCoordinateCodomain.lean`).
-/

namespace AlternatingAnalyticChallenge.Prop4_1

universe uK uE uE' uF

/-- Precomposition `A^k_{E,E';F}` has a bounded `k`-linear lift: a continuous `k`-linear map on
`L(E,E')` whose diagonal is `f ↦ (m ↦ m ∘ (f, …, f))`. -/
def HasBoundedLift (K : Type uK) [NontriviallyNormedField K] (k : ℕ)
    (E : Type uE) (E' : Type uE') (F : Type uF)
    [NormedAddCommGroup E] [NormedSpace K E] [NormedAddCommGroup E'] [NormedSpace K E']
    [NormedAddCommGroup F] [NormedSpace K F] : Prop :=
  ∃ P : (E →L[K] E') [×k]→L[K] ((E' [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F)),
    ∀ f : E →L[K] E', P (fun _ => f) = ContinuousAlternatingMap.compContinuousLinearMapCLM f

/-- A bounded linear retraction `ρ` of the inclusion
`Alt^k(E;F) ↪ Mult^k(E;F)` gives, for every normed `E'`, a bounded `k`-linear lift of
`A^k_{E,E';F}` of norm at most `‖ρ‖`. -/
theorem lift_of_retraction
    (K : Type uK) [NontriviallyNormedField K] (k : ℕ)
    (E : Type uE) (E' : Type uE') (F : Type uF)
    [NormedAddCommGroup E] [NormedSpace K E] [NormedAddCommGroup E'] [NormedSpace K E']
    [NormedAddCommGroup F] [NormedSpace K F]
    (ρ : (E [×k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F))
    (hρ : ∀ m : E [⋀^Fin k]→L[K] F, ρ m.toContinuousMultilinearMap = m) :
    ∃ P : (E →L[K] E') [×k]→L[K] ((E' [⋀^Fin k]→L[K] F) →L[K] (E [⋀^Fin k]→L[K] F)),
      (∀ f : E →L[K] E', P (fun _ => f) = ContinuousAlternatingMap.compContinuousLinearMapCLM f) ∧
      ∀ (f : Fin k → E →L[K] E') (m : E' [⋀^Fin k]→L[K] F) (x : Fin k → E),
        ‖P f m x‖ ≤ ‖ρ‖ * ‖m‖ * (∏ i, ‖f i‖) * ∏ j, ‖x j‖ :=
  ⟨AlternatingAnalytic.contractingRetractionLift (E' := E') k ρ,
    AlternatingAnalytic.contractingRetractionLift_diag k ρ hρ,
    AlternatingAnalytic.norm_contractingRetractionLift_apply_le k ρ⟩

/-- If `k! ≠ 0` in `K`, precomposition has a bounded `k`-linear lift. -/
theorem part1
    (K : Type uK) [NontriviallyNormedField K] (k : ℕ)
    (E : Type uE) (E' : Type uE') (F : Type uF)
    [NormedAddCommGroup E] [NormedSpace K E] [NormedAddCommGroup E'] [NormedSpace K E']
    [NormedAddCommGroup F] [NormedSpace K F]
    (hk : (k.factorial : K) ≠ 0) :
    HasBoundedLift K k E E' F := by
  have hk' : ((Fintype.card (Fin k)).factorial : K) ≠ 0 := by simpa using hk
  obtain ⟨P, hP, -⟩ := lift_of_retraction K k E E' F
    (ContinuousAlternatingMap.altProj K E F)
    (ContinuousAlternatingMap.altProj_toContinuousMultilinearMap hk')
  exact ⟨P, hP⟩

/-- If `E` has a finite algebraic basis with
continuous coordinate functionals, precomposition has a bounded `k`-linear lift. -/
theorem part2_domain
    (K : Type uK) [NontriviallyNormedField K] (k : ℕ)
    (E : Type uE) (E' : Type uE') (F : Type uF)
    [NormedAddCommGroup E] [NormedSpace K E] [NormedAddCommGroup E'] [NormedSpace K E']
    [NormedAddCommGroup F] [NormedSpace K F]
    {d : ℕ} (b : Module.Basis (Fin d) K E) (hb : ∀ i, Continuous (b.coord i)) :
    HasBoundedLift K k E E' F :=
  ⟨AlternatingAnalytic.finiteCoordinateDomainLift (E' := E') (F := F) b hb k,
    AlternatingAnalytic.finiteCoordinateDomainLift_diag b hb k⟩

/-- If `E'` has a finite algebraic basis with
continuous coordinate functionals, precomposition has a bounded `k`-linear lift. -/
theorem part2_codomain
    (K : Type uK) [NontriviallyNormedField K] (k : ℕ)
    (E : Type uE) (E' : Type uE') (F : Type uF)
    [NormedAddCommGroup E] [NormedSpace K E] [NormedAddCommGroup E'] [NormedSpace K E']
    [NormedAddCommGroup F] [NormedSpace K F]
    {d : ℕ} (b : Module.Basis (Fin d) K E') (hb : ∀ i, Continuous (b.coord i)) :
    HasBoundedLift K k E E' F :=
  ⟨AlternatingAnalytic.finiteCoordinateCodomainLift (E := E) (F := F) b hb k,
    AlternatingAnalytic.finiteCoordinateCodomainLift_diag b hb k⟩

end AlternatingAnalyticChallenge.Prop4_1
