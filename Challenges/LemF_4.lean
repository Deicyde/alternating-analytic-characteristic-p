import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Lemma F.4 (finite fibre obstruction), p. 51

Paper setting: "Over a field κ, put V = κ^{k+1} and V' = κ^k. Write e_1, …, e_{k+1} and
e'_1, …, e'_k for their bases, ε^a for the coordinate forms on V, and δ' for the determinant on
V'. Set
  N = {ε^a : 1 ≤ a ≤ k+1} ∪ {ε^a + ε^b : 1 ≤ a < b ≤ k+1},
  Σ_ν = ker ν,  C'_s = {z : z_s = 0},  H'_{cd} = {z : z_c = z_d},
and consider the finite family of pairs
  F = {(V, H'_{cd}) : c < d} ∪ {(Σ_ν, C'_s) : ν ∈ N, 1 ≤ s ≤ k}.          (F.2)
Let g_0 : V → V' be the coordinate projection onto the first k coordinates."

Paper statement: "Suppose k! = 0 in κ. There is no k-linear map
  τ : Hom_κ(V, V')^k → Alt^k_κ(V; κ)
satisfying both
(1) τ(g_0, …, g_0) = δ' ∘ (g_0, …, g_0);
(2) for every (Σ, Σ') ∈ F, the restriction τ(g^1, …, g^k)|_{Σ^k} is zero whenever
    g^r(Σ) ⊆ Σ' for every r."

## Formalization notes

* `κ` is any field and `(k ! : κ) = 0`, which forces `k ≥ 2`.
* `V = Fin (k + 1) → κ` and `V' = Fin k → κ`. Indices are 0-based, so "c < d", "a < b" and "the
  first k coordinates" are read in `Fin`.
* `Hom_κ(V, V')` is `V →ₗ[κ] V'` and `Alt^k_κ(V; κ)` is `V [⋀^Fin k]→ₗ[κ] κ`, both algebraic as in
  the paper; `τ` is a `MultilinearMap`.
* `δ'` is `(Pi.basisFun κ (Fin k)).det`, and `g₀` is `LinearMap.funLeft κ κ Fin.castSucc`.
* Defined here: `coordForms` (`N`), `colEq` (`H'_{cd}`), `colZero` (`C'_s`), `pairFamily` (`F`),
  `firstCoords` (`g₀`), `detV'` (`δ'`), and the conditions `FibreCondition1`, `FibreCondition2`.
* In condition (2), "g^r(Σ) ⊆ Σ'" is `Σ.map (g r) ≤ Σ'`, and "the restriction to Σ^k is zero" is
  `τ g ξ = 0` whenever every `ξ r ∈ Σ`.
-/

namespace AlternatingAnalyticChallenge.LemF_4

universe u

variable (κ : Type u) [Field κ] (k : ℕ)

/-- The set `N` of linear forms `ε^a` and `ε^a + ε^b` (`a < b`) on `V = κ^{k+1}`. -/
def coordForms : Set ((Fin (k + 1) → κ) →ₗ[κ] κ) :=
  Set.range (fun a : Fin (k + 1) => LinearMap.proj (R := κ) (φ := fun _ => κ) a) ∪
    {ν | ∃ a b : Fin (k + 1), a < b ∧
      ν = LinearMap.proj (R := κ) (φ := fun _ => κ) a +
        LinearMap.proj (R := κ) (φ := fun _ => κ) b}

/-- `H'_{cd} = {z ∈ κ^k : z_c = z_d}`. -/
def colEq (c d : Fin k) : Submodule κ (Fin k → κ) :=
  LinearMap.ker
    (LinearMap.proj (R := κ) (φ := fun _ => κ) c - LinearMap.proj (R := κ) (φ := fun _ => κ) d)

/-- `C'_s = {z ∈ κ^k : z_s = 0}`. -/
def colZero (s : Fin k) : Submodule κ (Fin k → κ) :=
  LinearMap.ker (LinearMap.proj (R := κ) (φ := fun _ => κ) s)

/-- The finite family `F` of pairs `(Σ, Σ')` from (F.2). -/
def pairFamily : Set (Submodule κ (Fin (k + 1) → κ) × Submodule κ (Fin k → κ)) :=
  {P | ∃ c d : Fin k, c < d ∧ P = (⊤, colEq κ k c d)} ∪
    {P | ∃ ν ∈ coordForms κ k, ∃ s : Fin k, P = (LinearMap.ker ν, colZero κ k s)}

/-- The coordinate projection `g₀ : κ^{k+1} → κ^k` onto the first `k` coordinates. -/
def firstCoords : (Fin (k + 1) → κ) →ₗ[κ] (Fin k → κ) :=
  LinearMap.funLeft κ κ Fin.castSucc

/-- The determinant `δ'` on `V' = κ^k`. -/
noncomputable def detV' : (Fin k → κ) [⋀^Fin k]→ₗ[κ] κ :=
  (Pi.basisFun κ (Fin k)).det

/-- Condition (1): `τ(g₀, …, g₀) = δ' ∘ (g₀, …, g₀)`. -/
def FibreCondition1
    (τ : MultilinearMap κ (fun _ : Fin k => (Fin (k + 1) → κ) →ₗ[κ] (Fin k → κ))
      ((Fin (k + 1) → κ) [⋀^Fin k]→ₗ[κ] κ)) : Prop :=
  τ (fun _ => firstCoords κ k) = (detV' κ k).compLinearMap (firstCoords κ k)

/-- Condition (2): for every `(Σ, Σ') ∈ F`, `τ(g¹, …, gᵏ)` vanishes on `Σ^k` whenever every
`g^r` maps `Σ` into `Σ'`. -/
def FibreCondition2
    (τ : MultilinearMap κ (fun _ : Fin k => (Fin (k + 1) → κ) →ₗ[κ] (Fin k → κ))
      ((Fin (k + 1) → κ) [⋀^Fin k]→ₗ[κ] κ)) : Prop :=
  ∀ P ∈ pairFamily κ k, ∀ g : Fin k → ((Fin (k + 1) → κ) →ₗ[κ] (Fin k → κ)),
    (∀ r, P.1.map (g r) ≤ P.2) →
      ∀ ξ : Fin k → (Fin (k + 1) → κ), (∀ r, ξ r ∈ P.1) → τ g ξ = 0

/-- Lemma F.4: if `k! = 0` in `κ`, no `k`-linear map
`τ : Hom_κ(κ^{k+1}, κ^k)^k → Alt^k_κ(κ^{k+1}; κ)` satisfies both conditions (1) and (2). -/
theorem not_exists_fibre_map (hk : (k.factorial : κ) = 0) :
    ¬ ∃ τ : MultilinearMap κ (fun _ : Fin k => (Fin (k + 1) → κ) →ₗ[κ] (Fin k → κ))
        ((Fin (k + 1) → κ) [⋀^Fin k]→ₗ[κ] κ),
      FibreCondition1 κ k τ ∧ FibreCondition2 κ k τ := by
  sorry

end AlternatingAnalyticChallenge.LemF_4
