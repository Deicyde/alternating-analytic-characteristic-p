import AlternatingAnalytic.Algebra.ExteriorSupportDimension
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.GroupTheory.Perm.Sign
import AlternatingAnalytic.Algebra.FiniteFieldObstruction

/-!
# Theorem B.9 (multipliers over a finite field), p. 31

Solution file: unlike the challenge, it additionally imports the library modules that prove
the claim. Remarks below about imports describe the challenge file.

Setting (Appendix B.3, p. 31): `L` is a finite field, `V := L^ℕ` and `V_fin := L^(ℕ) ⊆ V` is the
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

Formalization notes:
* `V = ℕ → L`, `V_fin = ℕ →₀ L`; a finitely supported sequence enters `V` through its coercion
  to a function. `Λ^k_L E` is Mathlib's `⋀[L]^k E`; the wedge is `exteriorPower.ιMulti L k`.
* A `2k`-linear map `E^k × E'^k → W` is a multilinear map in the first `k` slots with values in
  multilinear maps of the last `k` slots (curried form, equivalent to `2k`-linearity).
* "Antisymmetric in the last k slots" is `Ψ u (x ∘ σ) = sign σ • Ψ u x` for every permutation
  `σ` (no separate vanishing-on-equal-inputs condition, matching the paper's word).
* The coordinatewise product `u x` is written `fun n => u n * x n` (in `V`) or the pointwise
  `Finsupp` product `u * x` (in `V_fin`, part (2) with `E₀ = V_fin`). In part (2) with `E₀ = V`,
  "finitely supported u, x" is `(Function.support (u j)).Finite` for every slot.
* `sdim` is the library definition `AlternatingAnalytic.exteriorSupportDim`
  (`AlternatingAnalytic/Algebra/ExteriorSupportDimension.lean`): the least `finrank` of a
  finite-dimensional subspace `W` with `ω ∈ range (Λ^k W → Λ^k V)`, i.e. Definition B.1. That
  module is imported only for this definition; the theorem is proved in
  `Algebra/FiniteFieldObstruction.lean` / `Algebra/FiniteFieldTheorem.lean`, not imported here.
  In part (1) sdim is computed in `Λ^k V`, in part (2) in `Λ^k E₀`, as in the paper.
* "Finite field" is `[Field L] [Finite L]`; "k ≥ 1" is `hk : 1 ≤ k` (implied by `k! = 0`).
* Part (2) is split into two theorems, one for `E₀ = V` and one for `E₀ = V_fin`.
* No new definitions are introduced.
-/

namespace AlternatingAnalyticChallenge.ThmB_9

universe u

/-- **Theorem B.9 (1).** Over a finite field with `k! = 0`, there is no `2k`-linear map
`Ψ : V_fin^k × V_fin^k → Λ^k V` that is antisymmetric in the vector slots, satisfies (Pol1) for
the multipliers `D_u x = ux`, and has uniformly bounded support dimension on inputs with entries
in `{0, ±1}`. -/
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

/-- **Theorem B.9 (2), `E₀ = V`.** Over a finite field with `k! = 0`, there is no `2k`-linear map
`Ψ : V^k × V^k → Λ^k V` that is antisymmetric in the vector slots, satisfies (Pol1) for all
finitely supported `u, x`, and has uniformly bounded support dimension. -/
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

/-- **Theorem B.9 (2), `E₀ = V_fin`.** Over a finite field with `k! = 0`, there is no `2k`-linear
map `Ψ : V_fin^k × V_fin^k → Λ^k V_fin` that is antisymmetric in the vector slots, satisfies
(Pol1), and has uniformly bounded support dimension. -/
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
