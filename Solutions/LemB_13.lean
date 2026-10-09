import AlternatingAnalytic.Algebra.DeterminantArray
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.Perm.Sign
import AlternatingAnalytic.Algebra.ClusterDiagonal

/-!
# Lemma B.13 (the diagonal), p. 34

Solution file: unlike the challenge, it additionally imports the library modules that prove
the claim. Remarks below about imports describe the challenge file.

Setting (Appendix B.3-B.6): as for Lemma B.11. `L` is a finite field, `Ψ : V_fin^k × V_fin^k →
Λ^k V` is `2k`-linear, antisymmetric in the last `k` slots (hypothesis (a) of Theorem B.9(1)) and
satisfies (Pol1) for the multipliers `D_u x = ux` (hypothesis (b)); `H` is an infinite set on
which `T(a; y; c) = Ω_{Ψ(e_a; e_y)}(c)` depends only on the pattern; `χ(τ)` is the common value
of `χ(C₁, …, C_k)` over clusters `C₁, …, C_k` in `H` with order pattern `τ ∈ S_k`.

Paper statement: "∑_{τ ∈ S_k} χ(τ) = 1."

Formalization notes:
* Definitions introduced (identical in challenge and solution), mirroring Appendix B.3-B.5:
  `ClusterMap L k` (the curried `2k`-linear maps `V_fin^k × V_fin^k → Λ^k V`, `V = ℕ → L`,
  `V_fin = ℕ →₀ L`), `coeff` (the coefficients `T(a; y; c) = Ω_{Ψ(e_a; e_y)}(c)`),
  `PatternHomogeneous Ψ H` (the conclusion of Lemma B.10 for `T` with `N = 3k`, the 3k-tuple
  indexed by `Fin 3 × Fin k`, "same pattern" via the paper's comparison characterization),
  `IsCluster H C` (four consecutive elements of `H`), `HasOrderPattern C τ`, the weights
  `opWeight = s = (1,0,-1,0)`, `vecWeight = w = (1,-1,1,-1)`, the vectors `sC`, `wC`, and the
  cluster value `clusterValue = χ`.
* The determinant array `Ω : Λ^k (ℕ → L) → L^(ℕ^k)`, `Ω_{y₁∧⋯∧y_k}(c) = det(y_b(c_a))`, is the
  library definition `AlternatingAnalytic.determinantArray`
  (`AlternatingAnalytic/Algebra/DeterminantArray.lean`, with `determinantArray_ιMulti` giving
  the determinant formula); that module is imported only for this definition.
* Paper labels are 1-based, Lean's are 0-based: the cluster point `C(1)` is `C 0`, and the
  rank `τ(j) ∈ {1, …, k}` is `τ j : Fin k`.
* Context hypotheses. The lemma sits inside the proof of Theorem B.9, under the standing
  assumption that `Ψ` satisfies all hypotheses of Theorem B.9(1) with `k! = 0` in the finite
  field `L`. Taken literally that context is contradictory (Theorem B.9), which would make the
  statement vacuous. The challenge therefore keeps only the hypotheses the paper's proof uses
  (the standing objects `L` finite, `H` infinite with pattern homogeneity of `T`), and lists
  exactly which of Theorem B.9's hypotheses (a)-(c) are assumed; `k! = 0` is not assumed
  (Remark B.15 applies the same lemmas when `k! ≠ 0`).
* Hypotheses used here: multilinearity, (a) antisymmetry in the vector slots
  (`Ψ u (x ∘ σ) = sign σ • Ψ u x`), (b) (Pol1) for the multipliers (as in Theorem B.9(1)), and
  pattern homogeneity on `H`. The support bound (c) and `k! = 0` are not assumed (the paper
  notes the lemma "does not use that bound"). `[Finite L]` and `H.Infinite` are the standing
  context.
* `∑_τ χ(τ)` is formalized with an arbitrary choice of representatives: `R τ` is any `k`-tuple of
  clusters in `H` with order pattern `τ`, and the claim is `∑_τ χ(R τ) = 1`.
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

/-- **Lemma B.13 (the diagonal).** Under antisymmetry and (Pol1), `∑_{τ ∈ S_k} χ(τ) = 1`, where
`χ(τ)` is evaluated on any clusters in `H` with order pattern `τ`. -/
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
  exact AlternatingAnalytic.sum_clusterValue_order_eq_one Ψ hanti hpol H hhom (R 1)
    (fun j => (hR 1 j).1) (fun j p => (hR 1 j).2.1 p)
    (fun j l hjl p q => hRτ 1 j l (by simpa using hjl) p q) R
    (fun σ j => (hR σ j).1) (fun σ j p => (hR σ j).2.1 p) hRτ

end AlternatingAnalyticChallenge.LemB_13
