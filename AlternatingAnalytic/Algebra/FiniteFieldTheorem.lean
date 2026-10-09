import AlternatingAnalytic.Algebra.FiniteFieldObstruction

/-!
# The finite-field multiplier theorem

Theorem B.9: over a finite field with `k! = 0` there is no multiplier lift with bounded
support dimension. The proofs are in `FiniteFieldObstruction.lean`.
-/

open Finset Module
namespace AlternatingAnalytic

/-- Theorem B.9, with `V = ℕ → L` and `V_fin = ℕ →₀ L`. The first conjunct is part (1);
part (2) is split into the cases `E₀ = V` and `E₀ = V_fin`. -/
theorem finiteField_multiplier_theorem
    {L : Type*} [Field L] [Finite L] {k : ℕ}
    (hfactorial : (k.factorial : L) = 0) :
    (∀ (Ψ : ClusterMap L k)
    (_hanti : ClusterVectorAntisymmetric Ψ) (_hpol : ClusterPol1 Ψ)
    (d : ℕ) (_hbound : ∀ (u v : Fin k → ℕ →₀ L),
      (∀ j x, u j x = 0 ∨ u j x = 1 ∨ u j x = -1) →
      (∀ j x, v j x = 0 ∨ v j x = 1 ∨ v j x = -1) →
      exteriorSupportDim (Ψ u v) ≤ d) , False) ∧
    (∀ (Ψ : MultiplierMap L k (ℕ → L))
    (_hanti : ∀ (u v : Fin k → ℕ → L) (σ : Equiv.Perm (Fin k)),
      Ψ u (v ∘ σ) = Equiv.Perm.sign σ • Ψ u v)
    (_hpol : ∀ (u v : Fin k → ℕ →₀ L),
      (∑ σ : Equiv.Perm (Fin k), Ψ (fun j n => u (σ j) n) (fun j n => v j n)) =
        ∑ σ : Equiv.Perm (Fin k),
          exteriorPower.ιMulti L k (fun j n => u (σ j) n * v j n))
    (d : ℕ) (_hbound : ∀ (u v : Fin k → ℕ → L), exteriorSupportDim (Ψ u v) ≤ d) , False) ∧
    (∀ (Ψ : MultiplierMap L k (ℕ →₀ L))
    (_hanti : ∀ (u v : Fin k → ℕ →₀ L) (σ : Equiv.Perm (Fin k)),
      Ψ u (v ∘ σ) = Equiv.Perm.sign σ • Ψ u v)
    (_hpol : ∀ (u v : Fin k → ℕ →₀ L),
      (∑ σ : Equiv.Perm (Fin k), Ψ (u ∘ σ) v) =
        ∑ σ : Equiv.Perm (Fin k), exteriorPower.ιMulti L k (fun j => u (σ j) * v j))
    (d : ℕ) (_hbound : ∀ (u v : Fin k → ℕ →₀ L), exteriorSupportDim (Ψ u v) ≤ d) , False) := by
  exact ⟨finiteField_multiplier_obstruction hfactorial,
    finiteField_multiplier_obstruction_full hfactorial,
    finiteField_multiplier_obstruction_finsupp hfactorial⟩

end AlternatingAnalytic
