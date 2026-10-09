import AlternatingAnalytic.Algebra.ExteriorSupportDimension
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.GroupTheory.Perm.Sign

/-!
# Theorem B.9 (multipliers over a finite field), p. 33

Setting (Appendix B.3, p. 32): `L` is a finite field, `V := L^ℕ` and `V_fin := L^(ℕ) ⊆ V` is the
subspace of finitely supported sequences. For `u, x ∈ V`, `ux` is the coordinatewise product, so
`D_u x = ux` is the multiplier family. `sdim` is the support dimension of Definition B.1:
`sdim(ω) = min {dim W : W ⊆ V finite-dimensional, ω ∈ Λ^k W}`.

Paper statement: "Let L be a finite field and k ≥ 1 with k! = 0 in L.
(1) There is no 2k-linear map Ψ : V_fin^k × V_fin^k → Λ^k_L V over L such that
  (a) Ψ is antisymmetric in the last k slots;
  (b) Ψ satisfies (Pol1) for D_u x = ux: for all u₁, …, u_k, x₁, …, x_k ∈ V_fin,
      ∑_{σ ∈ S_k} Ψ(u_{σ(1)}, …, u_{σ(k)}; x₁, …, x_k) = ∑_{σ ∈ S_k} (u_{σ(1)} x₁) ∧ ⋯ ∧ (u_{σ(k)} x_k);
  (c) for some d ∈ ℕ, sdim(Ψ(u; x)) ≤ d for all u, x ∈ V_fin^k with entries in {0, ±1}.
(2) Let E₀ = V or E₀ = V_fin. There is no 2k-linear map Ψ : E₀^k × E₀^k → Λ^k_L E₀ over L that
  is antisymmetric in the last k slots, satisfies (Pol1) for all finitely supported u, x, and
  has sdim(Ψ(u; x)) ≤ d for all u, x ∈ E₀^k, for some d."

## Formalization notes
* `V = ℕ → L`, `V_fin = ℕ →₀ L`; a finitely supported sequence enters `V` through its coercion
  to a function. `Λ^k_L E` is `⋀[L]^k E`, with wedge `exteriorPower.ιMulti L k`.
* A `2k`-linear map is curried: multilinear in the first `k` slots, with values in multilinear
  maps of the last `k` slots.
* "Antisymmetric" is `Ψ u (x ∘ σ) = sign σ • Ψ u x` for every permutation `σ`.
* The product `ux` is `fun n => u n * x n` in `V` and the pointwise `Finsupp` product `u * x` in
  `V_fin`. For `E₀ = V`, "finitely supported" is `(Function.support (u j)).Finite`.
* `sdim` is `AlternatingAnalytic.exteriorSupportDim` (`Algebra/ExteriorSupportDimension.lean`),
  imported only for this definition. It is computed in `Λ^k V` in part (1) and in `Λ^k E₀` in
  part (2).
* Part (2) is split into two theorems, for `E₀ = V` and `E₀ = V_fin`.
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
  sorry

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
  sorry

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
  sorry

end AlternatingAnalyticChallenge.ThmB_9
