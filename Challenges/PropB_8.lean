import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.GroupTheory.Perm.Sign

/-!
# Proposition B.8 (pointwise versus polarized), p. 29

Setting (Appendix B.2, p. 28): fix a field `L`, an integer `k ≥ 1`, `L`-vector spaces `A` and
`V`, and a linear map `D : A → End_L(V)`, `a ↦ D_a`. A *lift of `D` in degree `k`* is a
`2k`-linear map `Ψ : A^k × V^k → Λ^k V` over `L` that is alternating in the `V`-slots. For
`f : [k] → [m]` and `b ∈ A^m` put `b_f := (b_{f(1)}, …, b_{f(k)})` and
`type f := (|f⁻¹(1)|, …, |f⁻¹(m)|) ∈ ℕ^m`.

* (Pw)   `Ψ(a, …, a; x₁, …, x_k) = D_a x₁ ∧ ⋯ ∧ D_a x_k` for all `a ∈ A`, `x ∈ V^k`.
* (Pol)  for all `m ≥ 1`, `b ∈ A^m`, `α ∈ ℕ^m` with `|α| = k`, and `x ∈ V^k`:
         `∑_{type f = α} Ψ(b_f; x) = ∑_{type f = α} D_{b_{f(1)}} x₁ ∧ ⋯ ∧ D_{b_{f(k)}} x_k`.
* (Pol1) for all `b₁, …, b_k ∈ A` and `x ∈ V^k`:
         `∑_{σ ∈ S_k} Ψ(b_{σ(1)}, …, b_{σ(k)}; x) = ∑_{σ ∈ S_k} D_{b_{σ(1)}} x₁ ∧ ⋯ ∧ D_{b_{σ(k)}} x_k`.

Paper statement: "Let Ψ be a lift of D in degree k over a field L.
(1) (Pol)⇒(Pw)⇒(Pol1), over every field.
(2) If L is infinite, or if L = F_q and k ≤ q, then (Pw)⇒(Pol).
(3) If L = F_q and k ≥ q + 1, then (Pw) does not imply (Pol) in general.
(4) If k! = 0 in L, then (Pol1) does not imply (Pw) in general."

Formalization notes:
* Definitions introduced (identical in challenge and solution): `Lift L A V k` is
  `MultilinearMap L (fun _ : Fin k => A) (V [⋀^Fin k]→ₗ[L] ⋀[L]^k V)`, i.e. a map multilinear in
  the `k` operator slots with values in Mathlib alternating maps of the `k` vector slots into
  Mathlib's exterior power `⋀[L]^k V` (in which a wedge with two equal factors vanishes, as in
  the paper). `typeOf f` is the multiplicity vector `type f`. `Pw`, `Pol`, `Pol1` are the three
  identities, with the wedge `exteriorPower.ιMulti L k`.
* `D : A → End_L(V)` is a linear map `A →ₗ[L] (V →ₗ[L] V)`.
* Index sets: `[k] = Fin k`, `[m] = Fin m`, `S_k = Equiv.Perm (Fin k)`; the paper's
  1-based labels become 0-based.
* "k ≥ 1" is the standing hypothesis `hk : 1 ≤ k` (in parts (3) and (4) it is implied by the
  other hypotheses and is still listed for uniformity).
* "L = F_q" is `[Finite L]` with `q = Nat.card L`; in part (2) the hypothesis "L infinite, or
  L = F_q and k ≤ q" is the disjunction `Infinite L ∨ (Finite L ∧ k ≤ Nat.card L)`.
* "Does not imply in general" (parts 3, 4) is formalized as the existence of `A`, `V`, `D` and a
  lift `Ψ` for which the first identity holds and the second fails. The witnesses `A`, `V` are
  required to live in the universe of `L`.
* No library module is imported: all notions are defined here from Mathlib.
-/

namespace AlternatingAnalyticChallenge.PropB_8

universe u v w

/-- A lift of `D` in degree `k`: a `2k`-linear map `Ψ : A^k × V^k → Λ^k V`, multilinear in the
`A`-slots and alternating in the `V`-slots. -/
abbrev Lift (L : Type u) [Field L] (A : Type v) [AddCommGroup A] [Module L A]
    (V : Type w) [AddCommGroup V] [Module L V] (k : ℕ) :=
  MultilinearMap L (fun _ : Fin k => A) (V [⋀^Fin k]→ₗ[L] ⋀[L]^k V)

/-- `type f = (|f⁻¹(1)|, …, |f⁻¹(m)|)` for a map `f : [k] → [m]`. -/
def typeOf {k m : ℕ} (f : Fin k → Fin m) (j : Fin m) : ℕ :=
  (Finset.univ.filter fun i => f i = j).card

section

variable {L : Type u} [Field L] {A : Type v} [AddCommGroup A] [Module L A]
  {V : Type w} [AddCommGroup V] [Module L V] {k : ℕ}

/-- The pointwise identity (Pw). -/
def Pw (D : A →ₗ[L] (V →ₗ[L] V)) (Ψ : Lift L A V k) : Prop :=
  ∀ (a : A) (x : Fin k → V),
    Ψ (fun _ => a) x = exteriorPower.ιMulti L k (fun i => D a (x i))

/-- The polarized identity (Pol): for all `m ≥ 1`, `b ∈ A^m`, `α ∈ ℕ^m` with `|α| = k` and
`x ∈ V^k`, the sums over the maps `f : [k] → [m]` of type `α` agree. -/
def Pol (D : A →ₗ[L] (V →ₗ[L] V)) (Ψ : Lift L A V k) : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ (b : Fin m → A) (α : Fin m → ℕ), ∑ j, α j = k →
    ∀ x : Fin k → V,
      ∑ f ∈ Finset.univ.filter (fun f : Fin k → Fin m => typeOf f = α),
          Ψ (fun i => b (f i)) x =
        ∑ f ∈ Finset.univ.filter (fun f : Fin k → Fin m => typeOf f = α),
          exteriorPower.ιMulti L k (fun i => D (b (f i)) (x i))

/-- The multilinear instance (Pol1) of the polarized identity. -/
def Pol1 (D : A →ₗ[L] (V →ₗ[L] V)) (Ψ : Lift L A V k) : Prop :=
  ∀ (b : Fin k → A) (x : Fin k → V),
    ∑ σ : Equiv.Perm (Fin k), Ψ (fun i => b (σ i)) x =
      ∑ σ : Equiv.Perm (Fin k), exteriorPower.ιMulti L k (fun i => D (b (σ i)) (x i))

end

/-- **Proposition B.8 (1).** Over every field, (Pol) ⇒ (Pw) ⇒ (Pol1). -/
theorem pol_imp_pw_and_pw_imp_pol1
    {L : Type u} [Field L] {A : Type v} [AddCommGroup A] [Module L A]
    {V : Type w} [AddCommGroup V] [Module L V] {k : ℕ} (hk : 1 ≤ k)
    (D : A →ₗ[L] (V →ₗ[L] V)) (Ψ : Lift L A V k) :
    (Pol D Ψ → Pw D Ψ) ∧ (Pw D Ψ → Pol1 D Ψ) := by
  sorry

/-- **Proposition B.8 (2).** If `L` is infinite, or `L = F_q` with `k ≤ q`, then (Pw) ⇒ (Pol). -/
theorem pw_imp_pol
    {L : Type u} [Field L] {A : Type v} [AddCommGroup A] [Module L A]
    {V : Type w} [AddCommGroup V] [Module L V] {k : ℕ} (hk : 1 ≤ k)
    (hL : Infinite L ∨ (Finite L ∧ k ≤ Nat.card L))
    (D : A →ₗ[L] (V →ₗ[L] V)) (Ψ : Lift L A V k) :
    Pw D Ψ → Pol D Ψ := by
  sorry

/-- **Proposition B.8 (3).** If `L = F_q` and `k ≥ q + 1`, then (Pw) does not imply (Pol) in
general: some lift satisfies (Pw) but not (Pol). -/
theorem exists_pw_not_pol
    {L : Type u} [Field L] [Finite L] {k : ℕ} (hk : 1 ≤ k) (hkq : Nat.card L + 1 ≤ k) :
    ∃ (A : Type u) (_ : AddCommGroup A) (_ : Module L A)
      (V : Type u) (_ : AddCommGroup V) (_ : Module L V)
      (D : A →ₗ[L] (V →ₗ[L] V)) (Ψ : Lift L A V k), Pw D Ψ ∧ ¬ Pol D Ψ := by
  sorry

/-- **Proposition B.8 (4).** If `k! = 0` in `L`, then (Pol1) does not imply (Pw) in general:
some lift satisfies (Pol1) but not (Pw). -/
theorem exists_pol1_not_pw
    {L : Type u} [Field L] {k : ℕ} (hk : 1 ≤ k) (hfact : (k.factorial : L) = 0) :
    ∃ (A : Type u) (_ : AddCommGroup A) (_ : Module L A)
      (V : Type u) (_ : AddCommGroup V) (_ : Module L V)
      (D : A →ₗ[L] (V →ₗ[L] V)) (Ψ : Lift L A V k), Pol1 D Ψ ∧ ¬ Pw D Ψ := by
  sorry

end AlternatingAnalyticChallenge.PropB_8
