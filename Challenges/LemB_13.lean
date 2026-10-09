import AlternatingAnalytic.Algebra.DeterminantArray
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.Perm.Sign

/-!
# Lemma B.13 (the diagonal), p. 34

Setting (Appendix B.3-B.6): as for Lemma B.11. `L` is a finite field, `Ψ : V_fin^k × V_fin^k →
Λ^k V` is `2k`-linear, antisymmetric in the last `k` slots (hypothesis (a) of Theorem B.9(1)) and
satisfies (Pol1) for the multipliers `D_u x = ux` (hypothesis (b)); `H` is an infinite set on
which `T(a; y; c) = Ω_{Ψ(e_a; e_y)}(c)` depends only on the pattern; `χ(τ)` is the common value
of `χ(C₁, …, C_k)` over clusters `C₁, …, C_k` in `H` with order pattern `τ ∈ S_k`.

Paper statement: "∑_{τ ∈ S_k} χ(τ) = 1."

## Formalization notes
* The definitions below follow Appendix B.3-B.5: `ClusterMap` (curried `2k`-linear maps, with
  `V = ℕ → L`, `V_fin = ℕ →₀ L`), `coeff` (= `T`), `PatternHomogeneous` (Lemma B.10 for `T`,
  with the `3k`-tuple indexed by `Fin 3 × Fin k`), `IsCluster`, `HasOrderPattern`, `opWeight`
  (= `s`), `vecWeight` (= `w`), `sC`, `wC` and `clusterValue` (= `χ`).
* `Ω` is `AlternatingAnalytic.determinantArray` (`Algebra/DeterminantArray.lean`), imported only
  for this definition.
* Labels are 0-based: `C(1)` is `C 0`, and the rank `τ(j)` is `τ j : Fin k`.
* The lemma sits inside the proof by contradiction of Theorem B.9, whose hypotheses with
  `k! = 0` are inconsistent. The statement keeps only what the proof uses: multilinearity,
  antisymmetry (a), (Pol1) for the multipliers (b), and pattern homogeneity on `H`. The bound (c)
  and `k! = 0` are not assumed.
* `[Finite L]` and `H.Infinite` are kept as standing context.
* `∑_τ χ(τ)` uses arbitrary representatives: `R τ` is any tuple of clusters in `H` with order
  pattern `τ`, and the claim is `∑_τ χ(R τ) = 1`.
-/

namespace AlternatingAnalyticChallenge.LemB_13

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

/-- Under antisymmetry and (Pol1), `∑_{τ ∈ S_k} χ(τ) = 1`, where `χ(τ)` is evaluated on any
clusters in `H` with order pattern `τ`. -/
theorem sum_clusterValue_eq_one
    {L : Type u} [Field L] [Finite L] {k : ℕ} (Ψ : ClusterMap L k)
    (H : Set ℕ) (hH : H.Infinite) (hhom : PatternHomogeneous Ψ H)
    (hanti : ∀ (u x : Fin k → ℕ →₀ L) (σ : Equiv.Perm (Fin k)),
      Ψ u (x ∘ σ) = Equiv.Perm.sign σ • Ψ u x)
    (hpol : ∀ u x : Fin k → ℕ →₀ L,
      ∑ σ : Equiv.Perm (Fin k), Ψ (fun j => u (σ j)) x =
        ∑ σ : Equiv.Perm (Fin k),
          exteriorPower.ιMulti L k (fun j => fun n => u (σ j) n * x j n))
    (R : Equiv.Perm (Fin k) → Fin k → Fin 4 → ℕ) (hR : ∀ τ j, IsCluster H (R τ j))
    (hRτ : ∀ τ, HasOrderPattern (R τ) τ) :
    ∑ τ : Equiv.Perm (Fin k), clusterValue Ψ (R τ) = 1 := by
  sorry

end AlternatingAnalyticChallenge.LemB_13
