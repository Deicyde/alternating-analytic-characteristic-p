import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Finset.Defs
import AlternatingAnalytic.Scalar.TestCertificate

/-!
# Lemma F.5 (finite test certificate), p. 52

Solution: the statement of `Challenges/LemF_5.lean`, proved from the library by
`AlternatingAnalytic.TestCertificate.exists_finite_test_certificate`
(`Scalar/TestCertificate.lean`), which combines the conditional certificate
`exists_finite_test_certificate_of_fibre` (`Scalar/TestCertificate/Certificate.lean`: tests are
base changes of `ZMod p`-rational tuples; duality over `ZMod p` replaces the paper's row
reduction) with Lemma F.4 over `ZMod p` (`AlternatingAnalytic.FibreObstruction.not_exists_fibre_map`).
The library repeats the definitions below verbatim in the namespace
`AlternatingAnalytic.TestCertificate`.
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
  exact AlternatingAnalytic.TestCertificate.exists_finite_test_certificate K k hk

end AlternatingAnalyticChallenge.LemF_5
