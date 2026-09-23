import AlternatingAnalytic.Algebra.FiniteFieldObstruction

/-! Both numbered parts of the paper's finite-field multiplier theorem, bundled. -/

open Finset Module
namespace AlternatingAnalytic

/-- The complete finite-field theorem: the ternary-input obstruction with exterior
output in all sequences, together with both full-sequence and finite-sequence
uniform-support versions. These are the two numbered parts of Theorem FF. -/
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
