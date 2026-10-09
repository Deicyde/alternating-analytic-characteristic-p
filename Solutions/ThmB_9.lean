import AlternatingAnalytic.Algebra.ExteriorSupportDimension
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.GroupTheory.Perm.Sign
import AlternatingAnalytic.Algebra.FiniteFieldObstruction

/-!
# Proof of Theorem B.9

Uses `AlternatingAnalytic.finiteField_multiplier_obstruction` and its `_full` and `_finsupp`
variants (`Algebra/FiniteFieldObstruction.lean`).
-/

namespace AlternatingAnalyticChallenge.ThmB_9

universe u

/-- Part (1): if `k! = 0` in the finite field `L`, no antisymmetric
`Ψ : V_fin^k × V_fin^k → Λ^k V` satisfies (Pol1) for `D_u x = ux` with sdim bounded on inputs
with entries in `{0, ±1}`. -/
theorem no_multiplier_lift_ternary_bound
    {L : Type u} [Field L] [Finite L] {k : ℕ} (hk : 1 ≤ k)
    (hfact : (k.factorial : L) = 0) :
    ¬ ∃ Ψ : MultilinearMap L (fun _ : Fin k => ℕ →₀ L)
        (MultilinearMap L (fun _ : Fin k => ℕ →₀ L) (⋀[L]^k (ℕ → L))),
      (∀ (u x : Fin k → ℕ →₀ L) (σ : Equiv.Perm (Fin k)),
        Ψ u (x ∘ σ) = Equiv.Perm.sign σ • Ψ u x) ∧
      (∀ u x : Fin k → ℕ →₀ L,
        ∑ σ : Equiv.Perm (Fin k), Ψ (fun j => u (σ j)) x =
          ∑ σ : Equiv.Perm (Fin k),
            exteriorPower.ιMulti L k (fun j => fun n => u (σ j) n * x j n)) ∧
      ∃ d : ℕ, ∀ u x : Fin k → ℕ →₀ L,
        (∀ j n, u j n = 0 ∨ u j n = 1 ∨ u j n = -1) →
        (∀ j n, x j n = 0 ∨ x j n = 1 ∨ x j n = -1) →
        AlternatingAnalytic.exteriorSupportDim (Ψ u x) ≤ d := by
  rintro ⟨Ψ, hanti, hpol, d, hbound⟩
  exact AlternatingAnalytic.finiteField_multiplier_obstruction hfact Ψ hanti hpol d hbound

/-- Part (2) for `E₀ = V`: if `k! = 0` in `L`, no antisymmetric `Ψ : V^k × V^k → Λ^k V`
satisfies (Pol1) on finitely supported inputs with bounded sdim. -/
theorem no_multiplier_lift_sequences
    {L : Type u} [Field L] [Finite L] {k : ℕ} (hk : 1 ≤ k)
    (hfact : (k.factorial : L) = 0) :
    ¬ ∃ Ψ : MultilinearMap L (fun _ : Fin k => ℕ → L)
        (MultilinearMap L (fun _ : Fin k => ℕ → L) (⋀[L]^k (ℕ → L))),
      (∀ (u x : Fin k → ℕ → L) (σ : Equiv.Perm (Fin k)),
        Ψ u (x ∘ σ) = Equiv.Perm.sign σ • Ψ u x) ∧
      (∀ u x : Fin k → ℕ → L,
        (∀ j, (Function.support (u j)).Finite) → (∀ j, (Function.support (x j)).Finite) →
        ∑ σ : Equiv.Perm (Fin k), Ψ (fun j => u (σ j)) x =
          ∑ σ : Equiv.Perm (Fin k),
            exteriorPower.ιMulti L k (fun j => fun n => u (σ j) n * x j n)) ∧
      ∃ d : ℕ, ∀ u x : Fin k → ℕ → L,
        AlternatingAnalytic.exteriorSupportDim (Ψ u x) ≤ d := by
  rintro ⟨Ψ, hanti, hpol, d, hbound⟩
  exact AlternatingAnalytic.finiteField_multiplier_obstruction_full hfact Ψ hanti
    (fun u v => hpol (fun j => ⇑(u j)) (fun j => ⇑(v j))
      (fun j => (u j).hasFiniteSupport) (fun j => (v j).hasFiniteSupport)) d hbound

/-- Part (2) for `E₀ = V_fin`: if `k! = 0` in `L`, no antisymmetric
`Ψ : V_fin^k × V_fin^k → Λ^k V_fin` satisfies (Pol1) with bounded sdim. -/
theorem no_multiplier_lift_finsupp
    {L : Type u} [Field L] [Finite L] {k : ℕ} (hk : 1 ≤ k)
    (hfact : (k.factorial : L) = 0) :
    ¬ ∃ Ψ : MultilinearMap L (fun _ : Fin k => ℕ →₀ L)
        (MultilinearMap L (fun _ : Fin k => ℕ →₀ L) (⋀[L]^k (ℕ →₀ L))),
      (∀ (u x : Fin k → ℕ →₀ L) (σ : Equiv.Perm (Fin k)),
        Ψ u (x ∘ σ) = Equiv.Perm.sign σ • Ψ u x) ∧
      (∀ u x : Fin k → ℕ →₀ L,
        ∑ σ : Equiv.Perm (Fin k), Ψ (fun j => u (σ j)) x =
          ∑ σ : Equiv.Perm (Fin k), exteriorPower.ιMulti L k (fun j => u (σ j) * x j)) ∧
      ∃ d : ℕ, ∀ u x : Fin k → ℕ →₀ L,
        AlternatingAnalytic.exteriorSupportDim (Ψ u x) ≤ d := by
  rintro ⟨Ψ, hanti, hpol, d, hbound⟩
  exact AlternatingAnalytic.finiteField_multiplier_obstruction_finsupp hfact Ψ hanti hpol d hbound

end AlternatingAnalyticChallenge.ThmB_9
