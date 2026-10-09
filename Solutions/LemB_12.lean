import AlternatingAnalytic.Algebra.DeterminantArray
import Mathlib.Data.Fin.VecNotation
import AlternatingAnalytic.Algebra.ClusterStaircase

/-!
# Proof of Lemma B.12

Uses `AlternatingAnalytic.clusterValue_adjacent_eq` (`Algebra/ClusterStaircase.lean`).
-/

namespace AlternatingAnalyticChallenge.LemB_12

universe u

open Finset

section ClusterDefinitions

variable {L : Type u} [Field L] {k : ℕ}

/-- A `2k`-linear map `Ψ : V_fin^k × V_fin^k → Λ^k V` (curried), `V = ℕ → L`, `V_fin = ℕ →₀ L`. -/
abbrev ClusterMap (L : Type u) [Field L] (k : ℕ) :=
  MultilinearMap L (fun _ : Fin k => ℕ →₀ L)
    (MultilinearMap L (fun _ : Fin k => ℕ →₀ L) (⋀[L]^k (ℕ → L)))

/-- The coefficients `T(a; y; c) := Ω_{Ψ(e_a; e_y)}(c₁, …, c_k)`, where `e_a = (e_{a₁}, …, e_{a_k})`
are unit vectors and `Ω` is the determinant array. -/
noncomputable def coeff (Ψ : ClusterMap L k) (a y c : Fin k → ℕ) : L :=
  AlternatingAnalytic.determinantArray
    (Ψ (fun j => Finsupp.single (a j) 1) (fun j => Finsupp.single (y j) 1)) c

/-- Pattern homogeneity of `T` on `H` (the output of Lemma B.10 with `N = 3k`): `T(a; y; c)`
depends only on the pattern of the `3k`-tuple `(a; y; c) ∈ H^{3k}`. The `3k`-tuple is indexed by
`Fin 3 × Fin k`: `(0, j) ↦ a_j`, `(1, j) ↦ y_j`, `(2, j) ↦ c_j`. -/
def PatternHomogeneous (Ψ : ClusterMap L k) (H : Set ℕ) : Prop :=
  ∀ z z' : Fin 3 × Fin k → ℕ, (∀ i, z i ∈ H) → (∀ i, z' i ∈ H) →
    (∀ i j, (z i < z j ↔ z' i < z' j) ∧ (z i = z j ↔ z' i = z' j)) →
    coeff Ψ (fun j => z (0, j)) (fun j => z (1, j)) (fun j => z (2, j)) =
      coeff Ψ (fun j => z' (0, j)) (fun j => z' (1, j)) (fun j => z' (2, j))

/-- A cluster `C = {h_n, h_{n+1}, h_{n+2}, h_{n+3}}`: four consecutive elements of `H`, listed
increasingly as `C 0 < C 1 < C 2 < C 3` (the paper's `C(1), …, C(4)`). -/
def IsCluster (H : Set ℕ) (C : Fin 4 → ℕ) : Prop :=
  StrictMono C ∧ (∀ p, C p ∈ H) ∧ ∀ x ∈ H, C 0 ≤ x → x ≤ C 3 → ∃ p, C p = x

/-- `(C₁, …, C_k)` has order pattern `τ`: `τ(j)` is the position of `C_j` among `C₁, …, C_k`,
i.e. `τ j < τ l` implies every element of `C_j` is below every element of `C_l`. -/
def HasOrderPattern (C : Fin k → Fin 4 → ℕ) (τ : Equiv.Perm (Fin k)) : Prop :=
  ∀ j l, τ j < τ l → ∀ p q, C j p < C l q

/-- The operator-slot weights `s = (1, 0, -1, 0)`. -/
def opWeight : Fin 4 → L := ![1, 0, -1, 0]

/-- The vector-slot weights `w = (1, -1, 1, -1)`. -/
def vecWeight : Fin 4 → L := ![1, -1, 1, -1]

/-- `s_C := ∑ᵢ sᵢ e_{C(i)}`. -/
noncomputable def sC (C : Fin 4 → ℕ) : ℕ →₀ L :=
  ∑ i, opWeight (L := L) i • Finsupp.single (C i) 1

/-- `w_C := ∑ᵢ wᵢ e_{C(i)}`. -/
noncomputable def wC (C : Fin 4 → ℕ) : ℕ →₀ L :=
  ∑ i, vecWeight (L := L) i • Finsupp.single (C i) 1

/-- The cluster value
`χ(C₁, …, C_k) := Ω_{Ψ(s_{C₁}, …, s_{C_k}; w_{C₁}, …, w_{C_k})}(C₁(1), …, C_k(1))`. -/
noncomputable def clusterValue (Ψ : ClusterMap L k) (C : Fin k → Fin 4 → ℕ) : L :=
  AlternatingAnalytic.determinantArray (Ψ (fun j => sC (C j)) (fun j => wC (C j)))
    (fun j => C j 0)

end ClusterDefinitions

/-- Exchanging two adjacent ranks `ℓ, ℓ + 1` of an order pattern does not change the cluster
value: `χ(τ) = χ(τ′)`. -/
theorem clusterValue_eq_of_adjacent_exchange
    {L : Type u} [Field L] [Finite L] {k : ℕ} (Ψ : ClusterMap L k)
    (H : Set ℕ) (hH : H.Infinite) (hhom : PatternHomogeneous Ψ H)
    (d : ℕ) (hbound : ∀ u x : Fin k → ℕ →₀ L,
      (∀ j n, u j n = 0 ∨ u j n = 1 ∨ u j n = -1) →
      (∀ j n, x j n = 0 ∨ x j n = 1 ∨ x j n = -1) →
      AlternatingAnalytic.exteriorSupportDim (Ψ u x) ≤ d)
    (τ τ' : Equiv.Perm (Fin k)) (α β : Fin k) (hαβ : α ≠ β)
    (hadj : (τ β).val = (τ α).val + 1)
    (hτ'α : τ' α = τ β) (hτ'β : τ' β = τ α) (hτ' : ∀ γ, γ ≠ α → γ ≠ β → τ' γ = τ γ)
    (C D : Fin k → Fin 4 → ℕ) (hC : ∀ j, IsCluster H (C j)) (hD : ∀ j, IsCluster H (D j))
    (hCτ : HasOrderPattern C τ) (hDτ' : HasOrderPattern D τ') :
    clusterValue Ψ C = clusterValue Ψ D := by
  have hτ'eq : τ' = (Equiv.swap α β).trans τ := by
    ext γ
    by_cases hγα : γ = α
    · subst hγα; simp [hτ'α]
    · by_cases hγβ : γ = β
      · subst hγβ; simp [hτ'β]
      · simp [hτ' γ hγα hγβ, Equiv.swap_apply_of_ne_of_ne hγα hγβ]
  subst hτ'eq
  exact AlternatingAnalytic.clusterValue_adjacent_eq Ψ H hH hhom d hbound τ α β hαβ hadj C D
    (fun j => (hC j).1) (fun j => (hD j).1) (fun j => (hC j).2.1) (fun j => (hD j).2.1)
    hCτ hDτ'

end AlternatingAnalyticChallenge.LemB_12
