import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Finset.Defs

/-!
# Lemma F.5 (finite test certificate), p. 52

Paper setting: as in Lemma F.4, now over the normed field K: "Give K^{k+1} and K^k their maximum
norms and use the same family (F.2) over K." Here V = K^{k+1}, V' = K^k, ε^a are the coordinate
forms, δ' is the determinant on V', N = {ε^a} ∪ {ε^a + ε^b : a < b},
F = {(V, H'_{cd}) : c < d} ∪ {(ker ν, C'_s) : ν ∈ N, 1 ≤ s ≤ k}, with
C'_s = {z : z_s = 0}, H'_{cd} = {z : z_c = z_d}, and g_0 : V → V' the projection onto the first k
coordinates. Throughout Appendix F, K has characteristic p > 0 and k ≥ p (equivalently k! = 0 in
K; the proof writes "char K = p").

Paper statement: "There are finite sets of tests T_j, one for each j = (Σ^j, Σ'^j) ∈ F, consisting
of tuples (g^1, …, g^k; ξ_1, …, ξ_k) with g^r Σ^j ⊆ Σ'^j and ξ_r ∈ Σ^j, such that every
K-multilinear τ satisfying condition (1) of Lemma F.4 obeys
  max_{j ∈ F} max_{(g; ξ) ∈ T_j} |τ(g^1, …, g^k)(ξ_1, …, ξ_k)| ≥ 1."           (F.5)

## Formalization notes
* The lemma as printed carries no explicit hypothesis; it relies on the standing hypothesis of
  Appendix F (`k! = 0` in `K`, i.e. characteristic `p > 0` and `k ≥ p`). It is added explicitly
  as `(k.factorial : K) = 0`. Without it the statement is false: if `k!` is invertible, the
  polarized determinant `τ(g¹, …, gᵏ) = (1/k!) Σ_σ δ' ∘ (g^{σ1}, …, g^{σk})` satisfies condition
  (1) and condition (2) of Lemma F.4, so every admissible test value is `0`.
* `K` is any normed field (`[NormedField K]`): no completeness, nontriviality or explicit
  nonarchimedean hypothesis (a normed field with `k! = 0` has positive characteristic and is
  automatically nonarchimedean, as the paper notes). The maximum norms on `K^{k+1}`, `K^k` do not
  enter the statement. The paper's proof (row reduction over `F_p`, `|c| = 1` for `c ∈ F_p^×`)
  uses none of the dropped standing hypotheses of Theorem F.1, so the strengthening is still true.
* `V = Fin (k + 1) → K`, `V' = Fin k → K`, `Hom_K(V, V') = V →ₗ[K] V'`, `Alt^k(V; K)` is the
  algebraic `V [⋀^Fin k]→ₗ[K] K`; `τ` is a `MultilinearMap` (no continuity, as in the paper).
  Indices are 0-based.
* The definitions `coordForms`, `colEq`, `colZero`, `pairFamily`, `firstCoords`, `detV'`,
  `FibreCondition1` are copied from the challenge for Lemma F.4 (with `κ` renamed `K`).
* The finite test sets are a function `T` from pairs of submodules to
  `Finset ((Fin k → (V →ₗ[K] V')) × (Fin k → V))`; only its values on members of `F` are
  constrained and used. "max ≥ 1" over finitely many tests is "some test has norm ≥ 1".
* Not formalized in the library: there is no proof to compare against.
-/

namespace AlternatingAnalyticChallenge.LemF_5

universe u

variable (K : Type u) [NormedField K] (k : ℕ)

/-- The set `N` of linear forms `ε^a` and `ε^a + ε^b` (`a < b`) on `V = K^{k+1}`. -/
def coordForms : Set ((Fin (k + 1) → K) →ₗ[K] K) :=
  Set.range (fun a : Fin (k + 1) => LinearMap.proj (R := K) (φ := fun _ => K) a) ∪
    {ν | ∃ a b : Fin (k + 1), a < b ∧
      ν = LinearMap.proj (R := K) (φ := fun _ => K) a +
        LinearMap.proj (R := K) (φ := fun _ => K) b}

/-- `H'_{cd} = {z ∈ K^k : z_c = z_d}`. -/
def colEq (c d : Fin k) : Submodule K (Fin k → K) :=
  LinearMap.ker
    (LinearMap.proj (R := K) (φ := fun _ => K) c - LinearMap.proj (R := K) (φ := fun _ => K) d)

/-- `C'_s = {z ∈ K^k : z_s = 0}`. -/
def colZero (s : Fin k) : Submodule K (Fin k → K) :=
  LinearMap.ker (LinearMap.proj (R := K) (φ := fun _ => K) s)

/-- The finite family `F` of pairs `(Σ, Σ')` from (F.2). -/
def pairFamily : Set (Submodule K (Fin (k + 1) → K) × Submodule K (Fin k → K)) :=
  {P | ∃ c d : Fin k, c < d ∧ P = (⊤, colEq K k c d)} ∪
    {P | ∃ ν ∈ coordForms K k, ∃ s : Fin k, P = (LinearMap.ker ν, colZero K k s)}

/-- The coordinate projection `g₀ : K^{k+1} → K^k` onto the first `k` coordinates. -/
def firstCoords : (Fin (k + 1) → K) →ₗ[K] (Fin k → K) :=
  LinearMap.funLeft K K Fin.castSucc

/-- The determinant `δ'` on `V' = K^k`. -/
noncomputable def detV' : (Fin k → K) [⋀^Fin k]→ₗ[K] K :=
  (Pi.basisFun K (Fin k)).det

/-- Condition (1): `τ(g₀, …, g₀) = δ' ∘ (g₀, …, g₀)`. -/
def FibreCondition1
    (τ : MultilinearMap K (fun _ : Fin k => (Fin (k + 1) → K) →ₗ[K] (Fin k → K))
      ((Fin (k + 1) → K) [⋀^Fin k]→ₗ[K] K)) : Prop :=
  τ (fun _ => firstCoords K k) = (detV' K k).compLinearMap (firstCoords K k)

/-- **Lemma F.5 (finite test certificate).** Assume `k! = 0` in `K`. There are finite sets of tests
`T j`, `j ∈ F`, of tuples `(g; ξ)` with every `g^r` mapping `Σ^j` into `Σ'^j` and every
`ξ_r ∈ Σ^j`, such that every `K`-multilinear `τ` satisfying condition (1) of Lemma F.4 has some
test value of absolute value at least `1`. -/
theorem exists_finite_test_certificate (hk : (k.factorial : K) = 0) :
    ∃ T : Submodule K (Fin (k + 1) → K) × Submodule K (Fin k → K) →
        Finset ((Fin k → ((Fin (k + 1) → K) →ₗ[K] (Fin k → K))) × (Fin k → (Fin (k + 1) → K))),
      (∀ j ∈ pairFamily K k, ∀ t ∈ T j,
        (∀ r, j.1.map (t.1 r) ≤ j.2) ∧ ∀ r, t.2 r ∈ j.1) ∧
      ∀ τ : MultilinearMap K (fun _ : Fin k => (Fin (k + 1) → K) →ₗ[K] (Fin k → K))
          ((Fin (k + 1) → K) [⋀^Fin k]→ₗ[K] K),
        FibreCondition1 K k τ →
          ∃ j ∈ pairFamily K k, ∃ t ∈ T j, 1 ≤ ‖τ t.1 t.2‖ := by
  sorry

end AlternatingAnalyticChallenge.LemF_5
